using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading;
using System.Collections;

using BoltFreezer.Interfaces;
using BoltFreezer.Utilities;
using BoltFreezer.DecompTools;

namespace BoltFreezer.PlanTools
{
    [Serializable]
    public class Plan : IEquatable<Plan>, IPlan
    {
        private static int Counter = -1;

        protected List<IPlanStep> steps;
        protected IState initial;
        protected IState goal;
        protected IPlanStep initialStep = null;
        protected IPlanStep goalStep = null;

        protected Graph<IPlanStep> orderings;
        protected List<CausalLink<IPlanStep>> causalLinks;
        public DecompositionLinks decomplinks;
        protected Flawque flaws;
        protected int decomps;
        protected int hdepth;
        public string id;

        public string ID
        {
            get { return id; }
            set { id = value; }
        }

        // Access the plan's steps.
        public List<IPlanStep> Steps
        {
            get { return steps; }
            set { steps = value; }
        }

        public IPlanStep GetStepByID(int id)
        {
            return steps.Single(s => s.ID == id);
        }

        // Access the plan's initial state.
        public IState Initial
        {
            get { return initial; }
            set { initial = value; }
        }

        // Access the plan's goal state.
        public IState Goal
        {
            get { return goal; }
            set { goal = value; }
        }

        // Access to plan's flaw library
        public Flawque Flaws
        {
            get { return flaws; }
            set { Flaws = value;  }
        }

        public int Decomps
        {
            get { return decomps; }
            set { decomps = value; }
        }

        public int Hdepth
        {
            get { return hdepth; }
            set { hdepth = value; }
        }

        // Access the plan's initial step.
        public IPlanStep InitialStep
        {
            get { return initialStep; }
            set { initialStep = value; }
        }

        // Access the plan's goal step.
        public IPlanStep GoalStep
        {
            get { return goalStep; }
            set { goalStep = value; }
        }

        // Access to plan's ordering graph
        public Graph<IPlanStep> Orderings
        {
            get { return orderings; }
            set   { throw new NotImplementedException(); }
        }

        // Access to plan's causal links
        public List<CausalLink<IPlanStep>> CausalLinks
        {
            get { return causalLinks; }
            set { causalLinks = value; }
        }

        public Plan ()
        {
            // S
            steps = new List<IPlanStep>();
            // O
            orderings = new Graph<IPlanStep>();
            // L
            causalLinks = new List<CausalLink<IPlanStep>>();
            // D
            decomplinks = new DecompositionLinks();
            // F 
            flaws = new Flawque();
            // I
            initial = new State();
            // G
            goal = new State();
            // d_i
            initialStep = new PlanStep(new Operator("initial", new List<IPredicate>(), initial.Predicates));
            // d_g
            goalStep = new PlanStep(new Operator("goal", goal.Predicates, new List<IPredicate>()));
            id = System.Threading.Interlocked.Increment(ref Counter).ToString();
        }

        public Plan(IState _initial, IState _goal)
        {
            steps = new List<IPlanStep>();
            causalLinks = new List<CausalLink<IPlanStep>>();
            orderings = new Graph<IPlanStep>();
            decomplinks = new DecompositionLinks();
            flaws = new Flawque();
            initial = _initial;
            goal = _goal;
            initialStep = new PlanStep(new Operator("initial", new List<IPredicate>(), initial.Predicates));
            goalStep = new PlanStep(new Operator("goal", goal.Predicates, new List<IPredicate>()));
            id = System.Threading.Interlocked.Increment(ref Counter).ToString();
        }

        public Plan(Operator _initial, Operator _goal)
        {
            steps = new List<IPlanStep>();
            causalLinks = new List<CausalLink<IPlanStep>>();
            orderings = new Graph<IPlanStep>();
            flaws = new Flawque();
            decomplinks = new DecompositionLinks();
            initial = new State(_initial.Effects);
            goal = new State(_goal.Preconditions);
            initialStep = new PlanStep(_initial);
            goalStep = new PlanStep(_goal);
            id = System.Threading.Interlocked.Increment(ref Counter).ToString();
        }

        // Used when cloning a plan: <S, O, L, D>, F
        public Plan(List<IPlanStep> steps, IState initial, IState goal, IPlanStep initialStep, IPlanStep goalStep, Graph<IPlanStep> orderings, List<CausalLink<IPlanStep>> causalLinks, DecompositionLinks dlinks, Flawque flaws)
        {
            this.steps = steps;
            this.causalLinks = causalLinks;
            this.orderings = orderings;
            this.decomplinks = dlinks;
            this.flaws = flaws;
            this.initial = initial;
            this.goal = goal;
            this.initialStep = initialStep;
            this.goalStep = goalStep;
            id = System.Threading.Interlocked.Increment(ref Counter).ToString();
        }

        public void Insert(IPlanStep newStep)
        {
            if (newStep.Height > 0)
            {
                InsertDecomp(newStep as ICompositePlanStep);
            }
            else
            {
                InsertPrimitive(newStep);
            }
        }

        public void InsertPrimitive(IPlanStep newStep)
        {
            steps.Add(newStep);
            orderings.Insert(InitialStep, newStep);
            orderings.Insert(newStep, GoalStep);

            // Add new flaws
            foreach (var pre in newStep.OpenConditions)
            {
                Flaws.Add(this, new OpenCondition(pre, newStep));
            }

            //Flaws.UpdateFlaws(this, newStep);
            // Don't update open conditions until this newStep has ordering wrt s_{need}

            // Don't check for threats when inserting.
        }

        public void InsertPrimitiveSubstep(IPlanStep newStep, List<IPredicate> init, bool isGoal)
        {
            steps.Add(newStep);
            orderings.Insert(InitialStep, newStep);
            orderings.Insert(newStep, GoalStep);

            // Add new flaws
            foreach (var pre in newStep.OpenConditions)
            {
                var newOC = new OpenCondition(pre, newStep);
                
                if (isGoal)
                {
                    newOC.isDummyGoal = true;
                }

                if (init.Contains(pre))
                {
                    newOC.hasDummyInit = true;
                    CausalLinks.Add(new CausalLink<IPlanStep>(pre, newStep.InitCndt, newStep));
                  //  newStep.Fulfill(pre);
                    continue;
                }

                Flaws.Add(this, newOC);
            }
        }

        public void InsertDecomp(ICompositePlanStep newStep)
        {
            this.hdepth += newStep.SubSteps.Count;
            decomps += 1;
            var IDMap = new Dictionary<int, IPlanStep>();

            // Clone, Add, and Order Initial step
            var dummyInit = new PlanStep(newStep.InitialStep) as IPlanStep;
            dummyInit.InitCndt = newStep.InitialStep.InitCndt;

            dummyInit.Depth = newStep.Depth;
            IDMap[newStep.InitialStep.ID] = dummyInit;
            steps.Add(dummyInit);
            orderings.Insert(InitialStep, dummyInit);
            orderings.Insert(dummyInit, GoalStep);

            // Clone, Add, and order Goal step
            var dummyGoal = new PlanStep(newStep.GoalStep) as IPlanStep;
            dummyGoal.Depth = newStep.Depth;
            dummyGoal.InitCndt = dummyInit;
            dummyGoal.GoalCndt = newStep.GoalStep.GoalCndt;
            InsertPrimitiveSubstep(dummyGoal, dummyInit.Effects, true);
            IDMap[newStep.GoalStep.ID] = dummyGoal;
            orderings.Insert(dummyInit, dummyGoal);

            dummyInit.GoalCndt = dummyGoal;

            // Officially add this step to the list of steps (DO NOT INSERT which would insert its flaws)
            steps.Add(newStep);

            // Create new list of substeps
            var newSubSteps = new List<IPlanStep>();

            // Blank out this step's preconditions and effects so that it cannot be used?
            newStep.Preconditions = new List<IPredicate>();
            newStep.Effects = new List<IPredicate>();

            // Assign new step's dummy initial and goal steps
            newStep.InitialStep = dummyInit;
            newStep.GoalStep = dummyGoal;

            // Insert decomp links for the dummy initial and goal steps
            decomplinks.Insert(newStep, dummyGoal);
            decomplinks.Insert(newStep, dummyInit);
            
            // For each substep, assign depth and insert into plan.
            foreach (var substep in newStep.SubSteps)
            {
                if (substep.Height > 0)
                {
                    // Don't just clone, create a new step so that it has a unique ID
                    var compositeSubStep = new CompositePlanStep(substep.Clone() as CompositePlanStep)
                    {
                        Depth = newStep.Depth + 1
                    };

                    newSubSteps.Add(compositeSubStep);
                    decomplinks.Insert(newStep, compositeSubStep);
                    Insert(compositeSubStep);

                    Orderings.Insert(compositeSubStep.GoalStep, dummyGoal);
                    Orderings.Insert(dummyInit, compositeSubStep.InitialStep);

                    IDMap[substep.ID] = compositeSubStep;

                    compositeSubStep.InitialStep.InitCndt = dummyInit;
                    compositeSubStep.GoalStep.GoalCndt = dummyGoal;
                }
                else
                {
                    var newsubstep = new PlanStep(substep.Clone() as IPlanStep)
                    {
                        Depth = newStep.Depth + 1
                    };

                    Orderings.Insert(newsubstep, dummyGoal);
                    Orderings.Insert(dummyInit, newsubstep);
                    IDMap[substep.ID] = newsubstep;
                    newSubSteps.Add(newsubstep);
                    newsubstep.InitCndt = dummyInit;
                    newsubstep.GoalCndt = dummyGoal;

                    decomplinks.Insert(newStep, newsubstep);

                    InsertPrimitiveSubstep(newsubstep, dummyInit.Effects, false);
                    
                    //if (newsubstep.Depth > Hdepth)
                    //{
                    //    Hdepth = newsubstep.Depth;
                    //}
                }
            }

            foreach (var tupleOrdering in newStep.SubOrderings)
            {

                // Don't bother adding orderings to dummies
                if (tupleOrdering.First.Equals(newStep.InitialStep))
                    continue;
                if (tupleOrdering.Second.Equals(newStep.GoalStep))
                    continue;

                var head = IDMap[tupleOrdering.First.ID];
                var tail = IDMap[tupleOrdering.Second.ID];
                if (head.Height > 0)
                {
                    // can you pass it back?
                    var temp = head as ICompositePlanStep;
                    head = temp.GoalStep as IPlanStep;
                }
                if (tail.Height > 0)
                {
                    var temp = tail as ICompositePlanStep;
                    tail = temp.InitialStep as IPlanStep;
                }
                Orderings.Insert(head, tail);
            }

            foreach (var clink in newStep.SubLinks)
            {
                var head = IDMap[clink.Head.ID];
                var tail = IDMap[clink.Tail.ID];
                if (head.Height > 0)
                {
                    var temp = head as CompositePlanStep;
                    head = temp.GoalStep as IPlanStep;
                }
                if (tail.Height > 0)
                {
                    var temp = tail as CompositePlanStep;
                    tail = temp.InitialStep as IPlanStep;
                }

                var newclink = new CausalLink<IPlanStep>(clink.Predicate, head, tail);
                if (tail.OpenConditions.Contains(clink.Predicate))
                {
                    tail.OpenConditions.Remove(clink.Predicate);
                }
                CausalLinks.Add(newclink);
                Orderings.Insert(head, tail);

                // check if this causal links is threatened by a step in subplan
                foreach (var step in newSubSteps)
                {
                    // Prerequisite criteria 1
                    if (step.ID == head.ID || step.ID == tail.ID)
                    {
                        continue;
                    }

                    // Prerequisite criteria 2
                    if (!CacheMaps.IsThreat(clink.Predicate, step))
                    {
                        continue;
                    }

                    // If the step has height, need to evaluate differently
                    if (step.Height > 0)
                    {
                        var temp = step as ICompositePlanStep;
                        if (Orderings.IsPath(head, temp.InitialStep))
                        {
                            continue;
                        }
                        if (Orderings.IsPath(temp.GoalStep, tail))
                        {
                            continue;
                        }
                    }
                    else
                    {
                        if (Orderings.IsPath(head, step))
                        {
                            continue;
                        }
                        if (Orderings.IsPath(step, tail))
                        {
                            continue;
                        }
                    }

                    Flaws.Add(new ThreatenedLinkFlaw(newclink, step));
                }
            }


            // This is needed because we'll check if these substeps are threatening links
            newStep.SubSteps = newSubSteps;
            newStep.InitialStep = dummyInit;
            newStep.GoalStep = dummyGoal;

            foreach (var pre in newStep.OpenConditions)
            {
                Flaws.Add(this, new OpenCondition(pre, dummyInit as IPlanStep));
            }

        }

        public IPlanStep Find(IPlanStep stepClonedFromOpenCondition)
        {
            if (GoalStep.Equals(stepClonedFromOpenCondition))
                return GoalStep;

            // For now, this condition is impossible
            if (InitialStep.Equals(stepClonedFromOpenCondition))
                return InitialStep;

            if (!Steps.Contains(stepClonedFromOpenCondition))
            {
                throw new System.Exception();
            }
            return Steps.Single(s => s.Equals(stepClonedFromOpenCondition));
        }

        public void Repair(OpenCondition oc, IPlanStep repairStep)
        {
            if (repairStep.Height > 0)
            {
                RepairWithComposite(oc, repairStep as CompositePlanStep);
            }
            else
            {
                RepairWithPrimitive(oc, repairStep);
            }
        }

        public void RepairWithPrimitive(OpenCondition oc, IPlanStep repairStep)
        {
            // oc = <needStep, needPrecond>. Need to find needStep in plan, because open conditions have been mutated before arrival.
            var needStep = Find(oc.step);

            //// we are fulfilling open conditions because open conditions can be used to add flaws.
            if (!needStep.Name.Equals("DummyGoal") && !needStep.Name.Equals("DummyInit"))
                needStep.Fulfill(oc.precondition);

            orderings.Insert(repairStep, needStep);
            var clink = new CausalLink<IPlanStep>(oc.precondition, repairStep, needStep);
            causalLinks.Add(clink);

            foreach (var step in Steps)
            {
                if (step.Height > 0)
                {
                    continue;
                }
                if (step.ID == repairStep.ID || step.ID == needStep.ID)
                {
                    continue;
                }
                if (!CacheMaps.IsThreat(oc.precondition, step))
                {
                    continue;
                }
                // step is a threat to need precondition
                if (Orderings.IsPath(needStep, step))
                {
                    continue;
                }
                if (Orderings.IsPath(step, repairStep))
                {
                    continue;
                }
                
                Flaws.Add(new ThreatenedLinkFlaw(clink, step));
            }
        }

        public void RepairWithComposite(OpenCondition oc, CompositePlanStep repairStep)
        {

            var needStep = Find(oc.step);
            if (!needStep.Name.Equals("DummyGoal") && !needStep.Name.Equals("DummyInit"))
                needStep.Fulfill(oc.precondition);

            orderings.Insert(repairStep.GoalStep as IPlanStep, needStep);
            //this.ID += string.Format("(^Orl[{0},{1}])", repairStep.GoalStep.ID, needStep.ID);

            // Causal Link between repair step's goal condition and need step.
            var clink = new CausalLink<IPlanStep>(oc.precondition, repairStep.GoalStep as IPlanStep, needStep);
            causalLinks.Add(clink);

            foreach (var step in Steps)
            {

                if (step.ID == repairStep.ID || step.ID == needStep.ID)
                {
                    continue;
                }
                if (!CacheMaps.IsThreat(oc.precondition, step))
                {
                    continue;
                }

                if (step.Height > 0)
                {

                    // we need to check that this step's goal step
                    var stepAsComp = step as CompositePlanStep;


                    if (decomplinks.OnDecompPath(clink.Head, step.ID))
                    {
                        // must be ordered within 
                        if (Orderings.IsPath(clink.Tail, stepAsComp.GoalStep))
                        {
                            // already tucked into Q's borders
                            continue;
                        }

                        if (!decomplinks.OnDecompPath(clink.Tail, step.ID))
                        {
                            // Special Case is when clink.Tail is goal step. Then we cannot tuck clink.Tail into borders.
                            if (clink.Tail.Equals(goalStep))
                            {
                                // We want to end this plan's existence, so we add a threat that cannot be resolved.
                                Flaws.Add(new ThreatenedLinkFlaw(clink, step));
                                continue;
                            }
                            // Q --> s -p-> t, not p in eff(Q), not Q --> t
                            // then, need to tuck t into Q's borders.

                            var tailRoot = GetStepByID(decomplinks.GetRoot(clink.Tail)) as CompositePlanStep;
                            Orderings.Insert(tailRoot.GoalStep, stepAsComp.InitialStep);
                            //this.ID += string.Format("(^Od[{0},{1}])", tailRoot.GoalStep.ID, stepAsComp.InitialStep.ID);
                        }

                        continue;
                    }

                    if (decomplinks.OnDecompPath(clink.Tail, step.ID))
                    {
                        // step cannot threaten
                        continue;
                    }


                    // step is a threat to need precondition
                    if (Orderings.IsPath(clink.Tail, stepAsComp.InitialStep))
                    {
                        continue;
                    }
                    if (Orderings.IsPath(stepAsComp.GoalStep, repairStep.InitialStep as IPlanStep))
                    {
                        continue;
                    }


                    Flaws.Add(new ThreatenedLinkFlaw(clink, stepAsComp));
                    // Flaws.Add(new ThreatenedLinkFlaw(clink, compInit));
                }

                else
                {
                    // is it possible that step is a sub-step of repair step? Yes it is.
                    if (decomplinks.OnDecompPath(step, repairStep.ID))
                    {
                        // but, there's nothing we can do about it; and all links to repairStep.GoalStep are there to be threatened
                        continue;
                    }

                    // step is a threat to need precondition
                    if (Orderings.IsPath(needStep, step))
                    {
                        continue;
                    }
                    if (Orderings.IsPath(step, repairStep.InitialStep as IPlanStep))
                    {
                        continue;
                    }

                    Flaws.Add(new ThreatenedLinkFlaw(clink, step));
                }

            }
        }

        public void DetectThreats(IPlanStep possibleThreat)
        {
            CompositePlanStep possibleThreatComposite = new CompositePlanStep();
            if (possibleThreat.Height > 0)
            {
                possibleThreatComposite = possibleThreat as CompositePlanStep;
            }

            foreach (var clink in causalLinks)
            {

                if (!CacheMaps.IsThreat(clink.Predicate, possibleThreat))
                {
                    continue;
                }

                if (possibleThreat.Height > 0)
                {

                    if (decomplinks.OnDecompPath(clink.Head, possibleThreat.ID))
                    {
                        // must be ordered within 
                        if (Orderings.IsPath(clink.Tail, possibleThreatComposite.GoalStep))
                        {
                            // already tucked into Q's borders
                            continue;
                        }

                        if (!decomplinks.OnDecompPath(clink.Tail, possibleThreat.ID))
                        {
                            // Q --> s -p-> t, not p in eff(Q), not Q --> t
                            // then, need to tuck t into Q's borders.
                            var tailRoot = GetStepByID(decomplinks.GetRoot(clink.Tail)) as CompositePlanStep;
                            Orderings.Insert(tailRoot.GoalStep, possibleThreatComposite.InitialStep);
                            //this.ID += string.Format("(^Od2[{0},{1}])", tailRoot.GoalStep.ID, possibleThreatComposite.InitialStep.ID);
                        }

                        continue;
                    }

                    if (decomplinks.OnDecompPath(clink.Tail, possibleThreat.ID))
                    {
                        continue;
                    }

                    if (Orderings.IsPath(clink.Tail, possibleThreatComposite.InitialStep))
                    {
                        continue;
                    }
                    if (Orderings.IsPath(possibleThreatComposite.GoalStep, clink.Head))
                    {
                        continue;
                    }
                    Flaws.Add(new ThreatenedLinkFlaw(clink, possibleThreat));
                }
                else
                {
                    // don't need to check decomp paths, because causal links and threat are all primitive. 
                    if (Orderings.IsPath(clink.Tail, possibleThreat))
                    {
                        continue;
                    }
                    if (Orderings.IsPath(possibleThreat, clink.Head))
                    {
                        continue;
                    }
                    Flaws.Add(new ThreatenedLinkFlaw(clink, possibleThreat));
                }


            }
        }

        public override bool Equals(object obj)
        {
            if (obj == null) return false;
            Plan objAsPart = obj as Plan;
            if (objAsPart == null) return false;
            else return Equals(objAsPart);
        }

        public override int GetHashCode()
        {
            int sumo = 0;
            foreach(var step in Steps)
            {
                sumo += 23 * step.GetHashCode();
            }
            foreach(var ordering in Orderings.edges)
            {
                sumo += 23 * ordering.GetHashCode();
            }
            foreach(var clink in CausalLinks)
            {
                sumo += 23 * clink.GetHashCode();
            }
            return sumo;
        }

        public bool Equals(Plan otherPlan)
        {
            // two plans are equal if they have the same steps, orderings, and causal links
            if (otherPlan.Steps.Count != this.Steps.Count)
            {
                return false;
            }
            if (otherPlan.Orderings.edges.Count != this.Orderings.edges.Count)
            {
                return false;
            }
            if (otherPlan.CausalLinks.Count != this.CausalLinks.Count)
            {
                return false;
            }

            // we need to check the step operator, not the planstep
            var stepActions = this.Steps.Select(step => step.Action);
            var otherStepActions = otherPlan.Steps.Select(step => step.Action);
            if (stepActions.Any(clink => !otherStepActions.Contains(clink)))
            {
                return false;
            }

            var orderingActions = this.Orderings.edges.Select(tup => new Tuple<IOperator, IOperator>(tup.First.Action, tup.Second.Action));
            var otherOrderingActions = otherPlan.Orderings.edges.Select(tup => new Tuple<IOperator, IOperator>(tup.First.Action, tup.Second.Action));
            if (orderingActions.Any(clink => !otherOrderingActions.Contains(clink)))
            {
                return false;
            }
            
            var clinkActions = this.CausalLinks.Select(clink => new CausalLink<IOperator>(clink.Predicate, clink.Head.Action, clink.Tail.Action));
            var otherClinkActions = otherPlan.CausalLinks.Select(clink => new CausalLink<IOperator>(clink.Predicate, clink.Head.Action, clink.Tail.Action));
            if (clinkActions.Any(clink=> !otherClinkActions.Contains(clink)))
            {
                return false;
            }


            return true;
        }

       
        // Return the first state of the plan.
        public State GetFirstState ()
        {
            return (State)Initial.Clone();
        }

        public List<IPlanStep> TopoSort()
        {
            List<IPlanStep> sortedList = new List<IPlanStep>();

            foreach (var item in Orderings.TopoSort(InitialStep))
            {
                if (item.Equals(InitialStep) || item.Equals(GoalStep))
                    continue;

                sortedList.Add(item);
            }

            return sortedList;

        }

        // Displays the contents of the plan.
        public override string ToString ()
        {
            return id.ToString();
            //StringBuilder sb = new StringBuilder();

            //foreach (var step in steps)
            //    sb.AppendLine(step.ToString());

            //return sb.ToString();
        }

        // Displays the contents of the plan.
        public string ToStringOrdered ()
        {
            StringBuilder sb = new StringBuilder();

            foreach (var step in TopoSort())
                sb.AppendLine(step.ToString());

            return sb.ToString();
        }

        // Creates a clone of the plan. (orderings, and Links are Read-only, so only their host containers are replaced)
        public Object Clone ()
        {
            List<IPlanStep> newSteps = new List<IPlanStep>();

            foreach (var step in steps)
            {
                // need clone because these have fulfilled conditions that are mutable.
                newSteps.Add(step.Clone() as IPlanStep);
            }

            // these are static read only things
            //IState newInitial = initial.Clone() as IState;
            //IState newGoal = goal.Clone() as IState;


            IPlanStep newInitialStep = initialStep.Clone() as IPlanStep;
            // need clone of goal step because this as fulfillable conditions
            IPlanStep newGoalStep = goalStep.Clone() as IPlanStep;

            // Assuming for now that members of the ordering graph are never mutated.  If they are, then a clone will keep references to mutated members
            Graph<IPlanStep> newOrderings = orderings.Clone() as Graph<IPlanStep>;

            // Causal Links are containers whose members are not mutated.
            List<CausalLink<IPlanStep>> newLinks = new List<CausalLink<IPlanStep>>();
            foreach (var cl in causalLinks)
            {
                newLinks.Add(cl as CausalLink<IPlanStep>);
                //newLinks.Add(cl.Clone() as CausalLink<IPlanStep>);
            }

            // Inherit all flaws, must clone very flaw
            Flawque flawList = flaws.Clone() as Flawque;

            //return new Plan(newSteps, newInitial, newGoal, newInitialStep, newGoalStep, newOrderings, newLinks, flawList);
            var p =  new Plan(newSteps, Initial, Goal, newInitialStep, newGoalStep, newOrderings, newLinks, decomplinks.Clone(), flawList)
            {
                Hdepth = hdepth,
                Decomps = decomps
            };
            p.id = id + p.id;
            return p;
        }
    }
}