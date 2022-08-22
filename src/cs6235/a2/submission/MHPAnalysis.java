package cs6235.a2.submission;

import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import cs6235.a2.AnalysisBase;
import cs6235.a2.Query;
import soot.Body;
import soot.Local;
import soot.PointsToAnalysis;
import soot.PointsToSet;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.jimple.DefinitionStmt;
import soot.jimple.EnterMonitorStmt;
import soot.jimple.ExitMonitorStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.ReturnStmt;
import soot.jimple.SpecialInvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.VirtualInvokeExpr;
import soot.jimple.spark.sets.DoublePointsToSet;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;
import soot.toolkits.graph.BriefUnitGraph;
import soot.toolkits.graph.UnitGraph;

public class MHPAnalysis extends AnalysisBase {
	String resultString="";
	@Override
	public String getResultString() {
		
		// TODO Auto-generated method stub
		return resultString;
	}

	@Override
	protected void internalTransform(String phaseName, Map<String, String> options) {
		/*************************************************************************/
		//say we want to obtain all classes in the scene that extend Thread
		SootClass threadClass = Scene.v().getSootClass("java.lang.Thread");
		List<SootClass> classes = Scene.v().getActiveHierarchy().getSubclassesOf(threadClass);
//		System.out.println(classes + " extend Thread");
//		System.out.println();
		

		//observe that it returned a bunch of library classes as well - you may filter them out by library classes, like so
		//create a copy, because getSubclassesOf returns an unmodifiable collection
		List<SootClass> threadClasses = new LinkedList<SootClass>(classes);
		threadClasses.removeIf(c -> c.isLibraryClass());
//		System.out.println("Thread classes: "+threadClasses);
//		System.out.println();
		/*************************************************************************/
	
//	Create map for kill,gen,m and n. Map<nodes>
	Map<Integer,HashSet<Integer>> killmap = new HashMap<Integer,HashSet<Integer>>();
	Map<Integer,HashSet<Integer>> genmap = new HashMap<Integer,HashSet<Integer>>();
	Map<Integer,HashSet<Integer>> outmap = new HashMap<Integer,HashSet<Integer>>();
	Map<Integer,HashSet<Integer>> mmap = new HashMap<Integer,HashSet<Integer>>();
	Map<Integer,HashSet<Integer>> notifySuccmap = new HashMap<Integer,HashSet<Integer>>();
	
	Map<Unit,Set<Unit>> notifyedgemap = new HashMap<Unit,Set<Unit>>();
	Map<Integer,Set<Integer>> startedgemap = new HashMap<Integer,Set<Integer>>();
	Map<Integer,Integer> joinedgemap = new HashMap<Integer,Integer>();
	Map<Integer,Unit> unitmap = new HashMap<Integer,Unit>();
	
//	Set<Unit> waitNodesset = new HashSet<Unit>();
	Map<Integer,PointsToSet> monitormap = new HashMap<Integer,PointsToSet>();	// monitor node, obj points to set.
	Map<Integer,Set<Integer>> monitorunitmap = new HashMap<Integer,Set<Integer>>(); // monitor node, integer inside monitor.
	Map<Integer,PointsToSet> notifymap = new HashMap<Integer,PointsToSet>();	//Notify node, obj points to set.
	Map<Integer,PointsToSet> notifyAllmap = new HashMap<Integer,PointsToSet>();	//NotifyAll node, obj points to set.
	Map<Integer,PointsToSet> waitmap = new HashMap<Integer,PointsToSet>();	//wait node, obj points to set.
//	Create a map of  <int,all units> (U) and Create a <unit,int> map (X) which tells if unit is a method call then which unit to run next.
//	Set<Unit> tempSet=new HashSet<Unit>();
//	Killmap.put()
	Map<SootMethod,Set<Integer>> methodUnitsmap = new HashMap<SootMethod,Set<Integer>>();
	Stack<SootMethod> methodstack = new Stack<SootMethod>();
	Stack<Set<Integer>> eachMethodUnits = new Stack<Set<Integer>>();
	Stack<Unit> callsitestack = new Stack<Unit>();
	SootClass mainClass = Scene.v().getMainClass();
	PointsToAnalysis pta = Scene.v().getPointsToAnalysis();
	CallGraph cg = Scene.v().getCallGraph();
	SootMethod mainMethod = mainClass.getMethodByName("main");
	methodstack.add(mainMethod);
	eachMethodUnits.add(new HashSet<Integer>());
	LinkedList<SootClass> threadl = new LinkedList<SootClass>(); //Each element unique even after analysing the thread.
	LinkedList<Integer> startl = new LinkedList<Integer>();
	Stack<Unit> wl = new Stack<Unit>();
	Map<Unit,UnitGraph> ugmap = new HashMap<Unit,UnitGraph>();
//	for each thread call make a copy.
	Map<Integer,UnitGraph> nodeCFGmap = new HashMap<Integer,UnitGraph>();
	//WL of units. for each unit find pred and add them to the stack. if pred is
//	a invoke statement (except thread creation (need a list (Each element unique) to remember them) (check variable's class extend thread and invoke statement is start method) ) then visit/analyse it first.
	//If the wl of units is empty and theradlist is empty then terminate. If only wl of units is empty then pop one thread creation list (threadlist) and add its head to wl of units.
	UnitGraph cfg = new BriefUnitGraph(mainMethod.getActiveBody());
	List<Unit> heads = cfg.getHeads();
	Unit head = heads.get(0);
	ugmap.put(head, cfg);
	wl.push(head);
	int unitcounter = 0;
	boolean secStageWLflag = true;	//to note that it is main class thread.start and not from threadclass node.
	LinkedList<Integer> secStageWL = new LinkedList<Integer>();
	while(!(wl.empty() && threadl.isEmpty() )){
//		System.out.println("***********************************");
		if(wl.empty()) {	// When any thread ends.
			methodUnitsmap.put(methodstack.pop(), eachMethodUnits.pop());
			callsitestack.clear();
			methodstack.clear();
			eachMethodUnits.clear();
//			ugmap.clear();
			SootClass classtoanalyse = threadl.poll();
			SootMethod runMethod = classtoanalyse.getMethodByName("run");
			methodstack.add(runMethod);
			eachMethodUnits.add(new HashSet<Integer>());
			UnitGraph newthreadcfg = new BriefUnitGraph(runMethod.getActiveBody());
			List<Unit> runheads = newthreadcfg.getHeads();
			Unit runhead = runheads.get(0);
			ugmap.put(runhead, newthreadcfg);
			wl.push(runhead);
			
			//To modify the startedgemap
			if(startedgemap.get(startl.peek())== null) {
				Set<Integer> oldstartedge = new HashSet<Integer>();
				oldstartedge.add(unitcounter);
				startedgemap.put(startl.poll(), oldstartedge);
			}else {
				Set<Integer> oldstartedge = startedgemap.get(startl.peek());
				oldstartedge.add(unitcounter);
				startedgemap.put(startl.poll(), oldstartedge);
			}
			secStageWLflag = false;
		}
		Unit unit = wl.pop();
//		if(unit.)
		unitmap.put(unitcounter++, unit);
		cfg = ugmap.get(unit);
		List<Unit> successors = cfg.getSuccsOf(unit);
		if(successors != null) {
			ListIterator<Unit> succ= successors.listIterator(); 
			while(succ.hasNext()) {		
				Unit temp = succ.next();
				if(!unitmap.containsValue(temp)) {	//To not add nodes which are already visited.
					wl.add(temp);
					ugmap.put(temp, cfg);						
					
				}
			}
		}
		if((!callsitestack.empty()) && callsitestack.peek().equals(unit)) {
			callsitestack.pop();
			if(methodUnitsmap.containsKey(methodstack.peek())) {
				Set<Integer> unitset = eachMethodUnits.pop();
				unitset.addAll(methodUnitsmap.get(methodstack.peek()));
				eachMethodUnits.push(unitset);
			}
			methodUnitsmap.put(methodstack.pop(),eachMethodUnits.pop());
//			System.out.println("methodunitmap:"+methodUnitsmap);
		}
		
		Set<Integer> unitset = eachMethodUnits.pop();
		unitset.add(unitcounter -1);
		eachMethodUnits.push(unitset);
		
//		System.out.println((unitcounter-1)+"Unit:"+unit);
//		System.out.println("ugmap:"+Arrays.asList(ugmap));
//		System.out.println("Worklist:"+wl);
//		System.out.println("Threadlist:"+threadl);
		Stmt stmt = (Stmt) unit;
		if(stmt instanceof DefinitionStmt) {
			DefinitionStmt ds = (DefinitionStmt) stmt;
			Value lhs = ds.getLeftOp();
			Value rhs = ds.getRightOp();
//			TODO: modify the below implementation
//			if(rhs instanceof VirtualInvokeExpr) {System.out.println("rhs ofdefinitionstmt = invokeExpr");
//				VirtualInvokeExpr vInvExpr= (VirtualInvokeExpr)rhs;
//				SootMethod calledmethod  = vInvExpr.getMethod();
//				Value base = vInvExpr.getBase();
//				PointsToSet pts = pta.reachingObjects((Local)base);
//	//			//cg.spark returns an instance of DoublePointsToSet
//	//			DoublePointsToSet doublePTS = (DoublePointsToSet) pta.reachingObjects(local);
//				
//				Set<Type> types = pts.possibleTypes();
//				System.out.println(base + ": types are " + types);
//				boolean threadClassflag = false;
//				//if you want to obtain the Soot Class corresponding to each of the ref types
//				for(Type type : types) {
//					if(type instanceof RefType) {
//						RefType ref = (RefType) type;
//						SootClass sC = ref.getSootClass();
//						if(threadClasses.contains(sC)) {
//							threadClassflag = true;
//						}
//					}
//					System.out.println(type);
//				}
//	//			simple method call.
//	//			add the units to the top of the stack.
//				UnitGraph newcfg = new BriefUnitGraph(calledmethod.getActiveBody());
//				List<Unit> newheads = newcfg.getHeads();
//				Unit newhead = newheads.get(0);
//				ugmap.put(newhead,newcfg);
//				wl.push(newhead);
//				System.out.println("Updated Worklist:"+wl);
//			}
				
			/*for each method call add to the working list Need call graph too.*/
			/*do not add the method if it present in wl or visitedmethod list. */
		}
//		else if (stmt instanceof EnterMonitorStmt) {
//			EnterMonitorStmt enterstmt = (EnterMonitorStmt)stmt;
//			
//		}
//		else if(stmt instanceof ExitMonitorStmt) {
//			EnterMonitorStmt enterstmt = (EnterMonitorStmt)stmt;
//		}
		else if (stmt instanceof InvokeStmt) {
			InvokeStmt invstmt = (InvokeStmt)stmt;
			if(invstmt.getInvokeExpr() instanceof VirtualInvokeExpr) {
//				System.out.println("Virtual invoke statement");
				VirtualInvokeExpr vInvExpr= (VirtualInvokeExpr)invstmt.getInvokeExpr();
				SootMethod calledmethod  = vInvExpr.getMethod();
				Value base = vInvExpr.getBase();
				PointsToSet pts = pta.reachingObjects((Local)base);
//				//cg.spark returns an instance of DoublePointsToSet
//				DoublePointsToSet doublePTS = (DoublePointsToSet) pta.reachingObjects(local);
				
				Set<Type> types = pts.possibleTypes();
//				System.out.println(base + ": types are " + types);
				boolean threadClassflag = false;
				//if you want to obtain the Soot Class corresponding to each of the ref types
				for(Type type : types) {
					if(type instanceof RefType) {
						RefType ref = (RefType) type;
						SootClass sC = ref.getSootClass();
						if(threadClasses.contains(sC)) {
							threadClassflag = true;
						}
					}
//					System.out.println(type);
				}
				
				if(threadClassflag && calledmethod.getName().equals("start")) {
					// that means thread creation.
					// add the target class to the threadlist.
					for(Type type : types) {
						if(type instanceof RefType) {
							RefType ref = (RefType) type;
							SootClass sC = ref.getSootClass();
							threadl.add(sC);
							startl.add(unitcounter-1);
							if(secStageWLflag) {
								secStageWL.add(unitcounter-1);
							}
						}
//						System.out.println(type);
					}
				}
				
				else if(threadClassflag && calledmethod.getName().equals("join")) {
					
				}
				else if(calledmethod.getName().equals("notify"))
				{
					notifymap.put(unitcounter - 1, pts);
				}
				else if(calledmethod.getName().equals("notifyAll")) {
					notifyAllmap.put(unitcounter - 1, pts);
				}
				else if(calledmethod.getName().equals("wait")) {
					waitmap.put(unitcounter - 1, pts);
				}
				else
				{
//					Iterator<Edge> targetEdges = cg.edgesOutOf(unit);
//					while(targetEdges.hasNext()) {
//						System.out.println("TargetEdges:"+(Edge)targetEdges.next());
//					}
//					simple method call.
//					Recheck that if it's Call graph says it can be from multiple class (A:foo() or B:foo()).
//					add the units to the top of the stack.
					for(Type type : types) {
						if(type instanceof RefType) {
							RefType ref = (RefType) type;
							SootClass sC = ref.getSootClass();
							SootMethod newMethod = sC.getMethodByName(calledmethod.getName());
							UnitGraph newcfg = new BriefUnitGraph(newMethod.getActiveBody());
							List<Unit> newheads = newcfg.getHeads();
							callsitestack.add(wl.peek());
							methodstack.add(calledmethod);
							eachMethodUnits.add(new HashSet<Integer>());
							Unit newhead = newheads.get(0);
							ugmap.put(newhead,newcfg);
							wl.push(newhead);
//							System.out.println("Updated Worklist:"+wl);
//							System.out.println("callsite:"+callsitestack);
							
						}
					}
				}
			}
			else if(invstmt.getInvokeExpr() instanceof SpecialInvokeExpr) {
//				System.out.println("Special invoke statement.");
				/* ignoring the constructors */
			}
		} else if (stmt instanceof ReturnStmt) {
			
		} else {
//			System.out.println("I do not care about this statement");
		}
//		System.out.println("***********************************");

	}
	if(!methodstack.isEmpty()) {
		methodUnitsmap.put(methodstack.pop(),eachMethodUnits.pop());
	}
//	System.out.println("unitmap: "+unitmap);
	
	
	
	Stack<Integer> syncobjunitstack = new Stack<Integer>();
	Stack<PointsToSet> syncobjptsstack = new Stack<PointsToSet>();
	Stack<Set<Integer>> eachmonitorunits = new Stack<Set<Integer>>();
	for(Map.Entry<Integer, Unit> unittraverse: unitmap.entrySet()) {
		Stmt stmt = (Stmt)(unittraverse.getValue());
		if(!syncobjptsstack.isEmpty() ) {
			if(stmt instanceof InvokeStmt) {
				InvokeStmt invstmt = (InvokeStmt)stmt;
				if(invstmt.getInvokeExpr() instanceof VirtualInvokeExpr) {
					VirtualInvokeExpr vInvExpr= (VirtualInvokeExpr)invstmt.getInvokeExpr();
					SootMethod calledmethod  = vInvExpr.getMethod();
					if(calledmethod.getName().equals("wait")) {
						continue;
					}
				}
			}
					
			Set<Integer> temp = eachmonitorunits.pop();
			temp.add(unittraverse.getKey());
			eachmonitorunits.push(temp);
//			monitorunitmap.put(unittraverse.getKey(),syncobjptsstack.peek());
		}
		if(stmt instanceof EnterMonitorStmt) {
			EnterMonitorStmt enterstmt = (EnterMonitorStmt)stmt;
			syncobjunitstack.push(unittraverse.getKey());
			syncobjptsstack.push(pta.reachingObjects((Local)enterstmt.getOp()));
			eachmonitorunits.push(new HashSet<Integer>());
//			PointsToSet pts_t2b = pta.reachingObjects(t2b);
//			System.out.println(pts_t1b.hasNonEmptyIntersection(pts_t2b));
		}
		else if(stmt instanceof ExitMonitorStmt) {
			ExitMonitorStmt exitstmt = (ExitMonitorStmt)stmt;
			Integer temp = syncobjunitstack.pop();
			monitormap.put(temp,syncobjptsstack.pop());
			Set<Integer> temp1 = eachmonitorunits.pop();
			monitorunitmap.put(temp, temp1);
			if(!syncobjptsstack.isEmpty()) {
				Set<Integer> temp2 = eachmonitorunits.pop();
				temp2.addAll(temp1);
				eachmonitorunits.push(temp2);
			}
//			syncobjptsstack.pop();
		}
	}
//	System.out.println("monitormap:"+monitormap);
//	System.out.println("monitorunitmap:"+monitorunitmap);
//	System.out.println("Notifymap:"+notifymap);
//	System.out.println("NotifyAllmap:"+notifyAllmap);
//	System.out.println("waitmap:"+waitmap);
//	System.out.println("MethodUnitsmap:"+methodUnitsmap);
//	System.out.println("ugmap (unit to cfg):"+ ugmap);

		
	for(Map.Entry<Integer, PointsToSet> notifynode: notifymap.entrySet()) {
		notifySuccmap.put(notifynode.getKey(), null);
	}
	for(Map.Entry<Integer, PointsToSet> notifynode: notifyAllmap.entrySet()) {
		notifySuccmap.put(notifynode.getKey(), null);
	}
//	System.out.println("NotifySuccmap (notifykey+notifyallkey):"+notifySuccmap);
//	System.out.println("2nd stage wl:"+secStageWL);
//	System.out.println("StartEdgeMap"+startedgemap);
//	TODO: 1. How to compute join node kill set (N(t)). 
//	2. should I initialize notifysucc for with empty set.
	
	for(Map.Entry<Integer, Unit> unittraverse: unitmap.entrySet()) {
		Integer unitnum = (Integer)unittraverse.getKey();
		Stmt stmt = (Stmt)(unittraverse.getValue());
		if(stmt instanceof EnterMonitorStmt) {
//			System.out.println("monitornum:"+unitnum);
				Set<Integer> tokill = monitorunitmap.get(unitnum);
				PointsToSet pts = pta.reachingObjects((Local)((EnterMonitorStmt)stmt).getOp());
				DoublePointsToSet doublePTS = (DoublePointsToSet)pta.reachingObjects((Local)((EnterMonitorStmt)stmt).getOp());
//				Set<Type> types = pts.possibleTypes();
//				for(Type type : types) {
//					if(type instanceof RefType) {
//						RefType ref = (RefType) type;
//						SootClass sC = ref.getSootClass();
//						System.out.println(type);
//					}
//					
//				}
				if(doublePTS.size() == 1) {
					for(Map.Entry<Integer, Set<Integer>> monitorunit: monitorunitmap.entrySet()) {
						Unit tempenterunit = unitmap.get(monitorunit.getKey());
						PointsToSet otherpts = pta.reachingObjects((Local)((EnterMonitorStmt)(Stmt)tempenterunit).getOp());
						DoublePointsToSet otherdoublePTS = (DoublePointsToSet)pta.reachingObjects((Local)((EnterMonitorStmt)tempenterunit).getOp());
						if(otherdoublePTS.size()==1) {
							if(pts.hasNonEmptyIntersection(otherpts)) {
//								System.out.println("unitid:"+unitnum);
								tokill.addAll(monitorunit.getValue());
							}
						}
					}
				}
			killmap.put(unitnum, (HashSet<Integer>)tokill);
			
			Set<Integer> tokillwait = monitorunitmap.get(unitnum);
			for(Map.Entry<Integer, PointsToSet> waitstmt: waitmap.entrySet()) {
				Integer waitnum = (Integer)waitstmt.getKey();
				PointsToSet ptswait = waitstmt.getValue();
				DoublePointsToSet doublePTSwait = (DoublePointsToSet)ptswait;
				if(doublePTS.size() == 1) {
					for(Map.Entry<Integer, Set<Integer>> monitorunit: monitorunitmap.entrySet()) {
						Unit tempenterunit = unitmap.get(monitorunit.getKey());
						PointsToSet otherpts = pta.reachingObjects((Local)((EnterMonitorStmt)(Stmt)tempenterunit).getOp());
						DoublePointsToSet otherdoublePTS = (DoublePointsToSet)pta.reachingObjects((Local)((EnterMonitorStmt)tempenterunit).getOp());
						if(otherdoublePTS.size()==1) {
							if(pts.hasNonEmptyIntersection(otherpts)) {
//								System.out.println("unitid:"+unitnum);
								tokillwait.addAll(monitorunit.getValue());
							}
						}
					}
				}
				killmap.put(waitnum, (HashSet<Integer>)tokillwait);
			}
		}
		else if(stmt instanceof InvokeStmt) {
			InvokeStmt invstmt = (InvokeStmt)stmt;
			if(invstmt.getInvokeExpr() instanceof VirtualInvokeExpr) {
//				System.out.println("Virtual invoke statement");
				VirtualInvokeExpr vInvExpr= (VirtualInvokeExpr)invstmt.getInvokeExpr();
				SootMethod calledmethod  = vInvExpr.getMethod();
				Value base = vInvExpr.getBase();
				PointsToSet pts = pta.reachingObjects((Local)base);
//				//cg.spark returns an instance of DoublePointsToSet
//				DoublePointsToSet doublePTS = (DoublePointsToSet) pta.reachingObjects(local);
				
				Set<Type> types = pts.possibleTypes();
//				System.out.println(base + ": types are " + types);
				boolean threadClassflag = false;
				//if you want to obtain the Soot Class corresponding to each of the ref types
				for(Type type : types) {
					if(type instanceof RefType) {
						RefType ref = (RefType) type;
						SootClass sC = ref.getSootClass();
						if(threadClasses.contains(sC)) {
							threadClassflag = true;
						}
					}
//					System.out.println(type);
				}
				/*
				 * //According to the algorithm.
				if(threadClassflag && calledmethod.getName().equals("notifyAll")) {
					Set<Integer> tokill = new HashSet<Integer>();
					for(Map.Entry<Integer, PointsToSet> waitnode: waitmap.entrySet()) {
						Integer m = (Integer)waitnode.getKey();
						PointsToSet ptsw = (PointsToSet)waitnode.getValue();
						if(pts.hasNonEmptyIntersection(ptsw)) {
							tokill.add(m);
						}
					}
					killmap.put(unitnum,(HashSet<Integer>)tokill);
				}
				else if(threadClassflag && calledmethod.getName().equals("notify")) {
					Set<Integer> tokill = new HashSet<Integer>();
					for(Map.Entry<Integer, PointsToSet> waitnode: waitmap.entrySet()) {
						Integer m = (Integer)waitnode.getKey();
						PointsToSet ptsw = (PointsToSet)waitnode.getValue();
						DoublePointsToSet doublePTS = (DoublePointsToSet) ptsw;
						if(pts.hasNonEmptyIntersection(ptsw)) {
							tokill.add(m);
						}
					}
					if(tokill.size() == 1)
						killmap.put(unitnum,(HashSet<Integer>)tokill);
					else
						killmap.put(unitnum,new HashSet<Integer>());
				}
				else */ if(threadClassflag && calledmethod.getName().equals("start")) {
					Set<Integer> toGen = new HashSet<Integer>();
					for(Type type : types) {
						if(type instanceof RefType) {
							RefType ref = (RefType) type;
							SootClass sC = ref.getSootClass();
							for(Map.Entry<SootMethod, Set<Integer>> methodtravtemp: methodUnitsmap.entrySet()) {
								SootMethod m = (SootMethod)methodtravtemp.getKey();
								//if you want to obtain the Soot Class corresponding to each of the ref types
								if(m.getDeclaringClass().getName().equals(sC.getName())) {
									if(m.getName().equals("run")) {
										Integer min = Integer.MAX_VALUE;
										for(Integer tempunit:methodtravtemp.getValue()) {
											if(min > tempunit) {
												min = tempunit;
											}
										}
										toGen.add(min);
										break;
									}
								}
							}
						}
					}
					genmap.put(unitnum,(HashSet<Integer>)toGen);
				}
				else if(threadClassflag && calledmethod.getName().equals("join")) {
					Set<Integer> tokill = new HashSet<Integer>();
					for(Type type : types) {
						if(type instanceof RefType) {
							RefType ref = (RefType) type;
							SootClass sC = ref.getSootClass();
							for(Map.Entry<SootMethod, Set<Integer>> methodtravtemp: methodUnitsmap.entrySet()) {
								SootMethod m = (SootMethod)methodtravtemp.getKey();
								//if you want to obtain the Soot Class corresponding to each of the ref types
								if(m.getDeclaringClass().getName().equals(sC.getName())) {
									if(m.getName().equals("run")) {
										Integer min = Integer.MAX_VALUE;
										Integer max = Integer.MIN_VALUE;
										for(Integer tempunit:methodtravtemp.getValue()) {
											if(min > tempunit) {
												min = tempunit;
											}
											if(max < tempunit) {
												max = tempunit;
											}
										}
										for(Integer tempunit= min; tempunit<=max;tempunit++)
											tokill.add(tempunit);
										break;
									}
								}
							}
						}
					}
					killmap.put(unitnum,(HashSet<Integer>)tokill);
				}
			}
		}
	}
//	System.out.println("Killmap:"+killmap);
//	System.out.println("Genmap:"+genmap);
	
	for(Map.Entry<Integer, Unit> unittraverse: unitmap.entrySet()) {
		Integer unitnum = (Integer)unittraverse.getKey();
		if(mmap.get(unitnum) == null) {
			mmap.put(unitnum, new HashSet<Integer>());
		}
		if(outmap.get(unitnum) == null) {
			outmap.put(unitnum, new HashSet<Integer>());
		}
		if(notifySuccmap.get(unitnum) == null) {
			notifySuccmap.put(unitnum, new HashSet<Integer>());
		}
	}
//	Map<Integer,HashSet<Integer>> killmap = new HashMap<Integer,HashSet<Integer>>();
//	Map<Integer,HashSet<Integer>> genmap = new HashMap<Integer,HashSet<Integer>>();
//	Map<Integer,HashSet<Integer>> outmap = new HashMap<Integer,HashSet<Integer>>();
//	Map<Integer,HashSet<Integer>> mmap = new HashMap<Integer,HashSet<Integer>>();
//	
//	Map<Unit,Set<Unit>> notifyedgemap = new HashMap<Unit,Set<Unit>>();
//	Map<Integer,Integer> startedgemap = new HashMap<Integer,Integer>();
//	Map<Integer,Integer> joinedgemap = new HashMap<Integer,Integer>();
//	Map<Integer,Set<Integer>> notifySuccmap = new HashMap<Integer,Set<Integer>>();
//	for(Map.Entry<Integer, PointsToSet> notifynode: notifymap.entrySet()) {
//		notifySuccmap.put(notifynode.getKey(), null);
//	}
//	for(Map.Entry<Integer, PointsToSet> notifynode: notifyAllmap.entrySet()) {
//		notifySuccmap.put(notifynode.getKey(), null);
//	}
	while(!secStageWL.isEmpty()) {
		Integer currentnode = secStageWL.remove();
		HashSet<Integer> msetn = (HashSet<Integer>)mmap.get(currentnode).clone();
		HashSet<Integer> outsetn = (HashSet<Integer>)outmap.get(currentnode).clone();
		HashSet<Integer> notifySuccsetn = (HashSet<Integer>)notifySuccmap.get(currentnode).clone();
		HashSet<Integer> gennotifyall = new HashSet<Integer>();
		if(notifymap.containsKey(currentnode))
		{
			Iterator<Integer> mitr = mmap.get(currentnode).iterator();
			while(mitr.hasNext()) {
				Integer m = mitr.next();
				if(waitmap.containsKey(m)) {
					notifySuccsetn.add(m);
				}
			}
			genmap.put(currentnode, notifySuccsetn);
			
		}
		else if(notifyAllmap.containsKey(currentnode)) {
			// Update the notify successors.
			Iterator<Integer> mitr = mmap.get(currentnode).iterator();
			while(mitr.hasNext()) {
				Integer m = mitr.next();
				if(waitmap.containsKey(m)) {
					notifySuccsetn.add(m);
				}
			}
			genmap.put(currentnode, notifySuccsetn);
			
			// get Gennotifyall;
			
			for(Map.Entry<Integer, PointsToSet> waitnode: waitmap.entrySet()) {
				Integer notifiedEntry = waitnode.getKey();
				notifiedEntry = notifiedEntry;
				for(Map.Entry<Integer, PointsToSet> otherwaitnode: waitmap.entrySet()) {
					Integer otherNotifiedEntry = otherwaitnode.getKey();
					otherNotifiedEntry = otherNotifiedEntry;
					PointsToSet ptsna = notifyAllmap.get(currentnode);
					PointsToSet ptsne = waitnode.getValue();
					PointsToSet ptsone = waitnode.getValue();
					if(ptsna.hasNonEmptyIntersection(ptsne) && ptsne.hasNonEmptyIntersection(ptsone)) {
//						gennotifyall.add(otherNotifiedEntry);
//						gennotifyall.add(notifiedEntry);
						HashSet<Integer> outmapwait1 = mmap.get(notifiedEntry);
						outmapwait1.add(currentnode);
						outmapwait1.add(otherNotifiedEntry);
						mmap.put(notifiedEntry, outmapwait1);
						HashSet<Integer> outmapwait2 = mmap.get(otherNotifiedEntry);
						outmapwait2.add(currentnode);
						outmapwait2.add(notifiedEntry);
						mmap.put(otherNotifiedEntry, outmapwait2);
						msetn.add(notifiedEntry);
						msetn.add(otherNotifiedEntry);
					}
					//both are on same object and there is one notifyall on same object.
				}
			}
		}
		
		boolean mmapotherflag = true;
		//To set mmap for begin node.
		for(Map.Entry<Integer, Set<Integer>> startnode: startedgemap.entrySet()) {
			Iterator<Integer> beginitr = startnode.getValue().iterator();
			while(beginitr.hasNext()) {
				Integer begin = beginitr.next();
				if(currentnode == begin) {
					HashSet<Integer> tempout = (HashSet<Integer>)outmap.get(startnode.getKey()).clone();
					//-N(t)
					Unit currentunit = unitmap.get(startnode.getKey());
					InvokeStmt invstmt = (InvokeStmt)currentunit;
					if(invstmt.getInvokeExpr() instanceof VirtualInvokeExpr) {
//						System.out.println("Virtual invoke statement");
						VirtualInvokeExpr vInvExpr= (VirtualInvokeExpr)invstmt.getInvokeExpr();
						SootMethod calledmethod  = vInvExpr.getMethod();
						Value base = vInvExpr.getBase();
						PointsToSet pts = pta.reachingObjects((Local)base);
//						//cg.spark returns an instance of DoublePointsToSet
//						DoublePointsToSet doublePTS = (DoublePointsToSet) pta.reachingObjects(local);
						
						Set<Type> types = pts.possibleTypes();
//						System.out.println(base + ": types are " + types);
						boolean threadClassflag = false;
						//if you want to obtain the Soot Class corresponding to each of the ref types
						for(Type type : types) {
							if(type instanceof RefType) {
								RefType ref = (RefType) type;
								SootClass sC = ref.getSootClass();
								if(threadClasses.contains(sC)) {
									threadClassflag = true;
								}
							}
//							System.out.println(type);
						}
						if(threadClassflag && calledmethod.getName().equals("start")) {
							Set<Integer> toGen = new HashSet<Integer>();
							for(Type type : types) {
								if(type instanceof RefType) {
									RefType ref = (RefType) type;
									SootClass sC = ref.getSootClass();
									for(Map.Entry<SootMethod, Set<Integer>> methodtravtemp: methodUnitsmap.entrySet()) {
										SootMethod m = (SootMethod)methodtravtemp.getKey();
										//if you want to obtain the Soot Class corresponding to each of the ref types
										if(m.getDeclaringClass().getName().equals(sC.getName())) {
											if(m.getName().equals("run")) {
												Integer min = Integer.MAX_VALUE;
												Integer max = Integer.MIN_VALUE;
												for(Integer tempunit:methodtravtemp.getValue()) {
													if(min > tempunit) {
														min = tempunit;
													}
													if(max < tempunit) {
														max = tempunit;
													}
												}
												for(Integer tempunit= min; tempunit<=max;tempunit++)
													tempout.remove(tempunit);
												break;
											}
										}
									}
								}
							}
						}
					}
//					SootMethod startmethod = (((InvokeStmt)currentunit).getInvokeExpr()).getMethod();
//					if(methodUnitsmap.get(startmethod) != null)
//						tempout.removeAll(methodUnitsmap.get(startmethod));
//					if(ugmap.containsKey(currentunit))
//						System.out.println("Contain current key and cfg can be used.");
					msetn.addAll(tempout);
					//Reverse map
					Iterator<Integer> revmapitr = tempout.iterator();
					while(revmapitr.hasNext()) {
						Integer revmapnode = revmapitr.next();
//						in mmap of revmap.next add currentnode;
						HashSet<Integer> tempmap = mmap.get(revmapnode);
						tempmap.add(currentnode);
						mmap.put(revmapnode,tempmap);
					}
//					mmap.put(currentnode, tempout);
					mmapotherflag = false;
				}
			}
		}
		if(mmapotherflag) {
			//Simple function call the current node is first statement of function call.
			Integer prede;
			prede = -1;
			if(currentnode>0) {
				Stmt stmt = (Stmt)unitmap.get(currentnode-1);
				if(stmt instanceof InvokeStmt) {
					InvokeStmt invstmt = (InvokeStmt)stmt;
					if(invstmt.getInvokeExpr() instanceof VirtualInvokeExpr) {
						VirtualInvokeExpr vInvExpr= (VirtualInvokeExpr)invstmt.getInvokeExpr();
						SootMethod calledmethod  = vInvExpr.getMethod();
						Value base = vInvExpr.getBase();
						PointsToSet pts = pta.reachingObjects((Local)base);
		//				//cg.spark returns an instance of DoublePointsToSet
		//				DoublePointsToSet doublePTS = (DoublePointsToSet) pta.reachingObjects(local);
						
						Set<Type> types = pts.possibleTypes();
		//				System.out.println(base + ": types are " + types);
						boolean threadClassflag = false;
						//if you want to obtain the Soot Class corresponding to each of the ref types
						for(Type type : types) {
							if(type instanceof RefType) {
								RefType ref = (RefType) type;
								SootClass sC = ref.getSootClass();
								if(threadClasses.contains(sC)) {
									threadClassflag = true;
								}
							}
		//					System.out.println(type);
						}
						if(!(threadClassflag && (calledmethod.getName().equals("start") || calledmethod.getName().equals("join") ))) {		//Not a thread creation statement.
							prede = currentnode-1;
						}
					}
				}
			}
			
			if(prede!=-1) {
				msetn.addAll(outmap.get(prede));
				Iterator<Integer> revmapitr = outmap.get(prede).iterator();
				while(revmapitr.hasNext()) {
					Integer revmapnode = revmapitr.next();
//					in mmap of revmap.next add currentnode;
					HashSet<Integer> tempmap = mmap.get(revmapnode);
					tempmap.add(currentnode);
					mmap.put(revmapnode,tempmap);
				}
			}
			else {
				Unit currentunit = unitmap.get(currentnode);
				UnitGraph currentnodecfg = ugmap.get(currentunit);
				List<Unit> predecessors = currentnodecfg.getPredsOf(currentunit);
				if(predecessors != null) {
					ListIterator<Unit> pred= predecessors.listIterator(); 
					while(pred.hasNext()) {	
						Unit temp = pred.next();
						
						Integer nodenum = -1;
						
						for(Map.Entry<Integer, Unit> node: unitmap.entrySet()) {
							if(node.getValue().equals(temp))
								nodenum = node.getKey();
	//							break;
						}
						if(nodenum!= -1 && outmap.get(nodenum)!=null && !outmap.get(nodenum).isEmpty()) {
							msetn.addAll(outmap.get(nodenum));
							Iterator<Integer> revmapitr = outmap.get(nodenum).iterator();
							while(revmapitr.hasNext()) {
								Integer revmapnode = revmapitr.next();
//								in mmap of revmap.next add currentnode;
								HashSet<Integer> tempmap = mmap.get(revmapnode);
								tempmap.add(currentnode);
								mmap.put(revmapnode,tempmap);
							}
						}
					}
				}
			}
		}
		// Input is propagated to output.
		
		
		
		

		outsetn.addAll(msetn);
		if(genmap.containsKey(currentnode))
			outsetn.addAll(genmap.get(currentnode));
		if(killmap.containsKey(currentnode))
			outsetn.removeAll(killmap.get(currentnode));
		
//		if(!notifySuccsetn.equals(notifySuccmap.get(currentnode))) {
//			secStageWL.addAll(unitmap.keySet());
//		}
//		System.out.println(secStageWL);
		
		if(!(msetn.equals(mmap.get(currentnode)) && outsetn.equals(outmap.get(currentnode)) && notifySuccsetn.equals(notifySuccmap.get(currentnode)))) {
			mmap.put(currentnode, msetn);
			outmap.put(currentnode, outsetn);
			notifySuccmap.put(currentnode, notifySuccsetn);
//			LinkedList<Integer> tempsecwl = new LinkedList<Integer>();
//			tempsecwl.unitmap.keySet();
			Iterator<Integer> tempwlnodeitr = unitmap.keySet().iterator();
			while(tempwlnodeitr.hasNext()) {
				Integer tempwlnode = tempwlnodeitr.next();
				if(!secStageWL.contains(tempwlnode))
					secStageWL.addAll(unitmap.keySet());
				//MAKE secStageWL as set.
			}
		}
	}
//	System.out.println(notifySuccmap);
//	System.out.println(mmap);
	
	
	//Result printing.
	List <Query> queries = this.getQueries();
//	System.out.println(queries);
	Iterator queryitr = queries.iterator();
	int count = 0;
	String[] result = new String[queries.size()];
	for(int i =0; i < queries.size();i++)
	{
		result[i] = "NO";
	}
	while(queryitr.hasNext()) {
		Query query = (Query)queryitr.next();
		String lhs = query.getLhs();
		String rhs = query.getRhs();
		String[] lhsarr = lhs.split(":");
		String lhsclass = lhsarr[0];
		String lhsmethod = lhsarr[1];
		String[] rhsarr = rhs.split(":");
		String rhsclass = rhsarr[0];
		String rhsmethod = rhsarr[1];
//		System.out.println("lhsclass:"+lhsclass+" lshmethod:"+lhsmethod+ " rhsclass:"+rhsclass+" rhsmethod:"+rhsmethod);
		for(Map.Entry<Integer, Unit> node: unitmap.entrySet()) {
			Integer unitnum = node.getKey();
			Unit unit = node.getValue();
			if(unit instanceof InvokeStmt) {
				InvokeStmt invstmt = (InvokeStmt)unit;
				if(invstmt.getInvokeExpr() instanceof VirtualInvokeExpr) {
//					System.out.println("Virtual invoke statement");
					VirtualInvokeExpr vInvExpr= (VirtualInvokeExpr)invstmt.getInvokeExpr();
					SootMethod calledmethod  = vInvExpr.getMethod();
					Value base = vInvExpr.getBase();
					PointsToSet pts = pta.reachingObjects((Local)base);
//					//cg.spark returns an instance of DoublePointsToSet
//					DoublePointsToSet doublePTS = (DoublePointsToSet) pta.reachingObjects(local);
					
					Set<Type> types = pts.possibleTypes();
//					System.out.println(base + ": types are " + types);
					boolean threadClassflag = false;
					//if you want to obtain the Soot Class corresponding to each of the ref types
					for(Type type : types) {
						if(type instanceof RefType) {
							RefType ref = (RefType) type;
							SootClass sC = ref.getSootClass();
							if(sC.getName().equals(lhsclass)) {
								if(calledmethod.getName().equals(lhsmethod)) {
									Iterator<Integer> msetitr = mmap.get(unitnum).iterator();
									while(msetitr.hasNext()) {
										Integer othernode = msetitr.next();
										Unit otherunit = unitmap.get(othernode);
										
										
										if(otherunit instanceof InvokeStmt) {
											InvokeStmt invstmt1 = (InvokeStmt)otherunit;
											if(invstmt1.getInvokeExpr() instanceof VirtualInvokeExpr) {
//												System.out.println("Virtual invoke statement");
												VirtualInvokeExpr vInvExpr1= (VirtualInvokeExpr)invstmt1.getInvokeExpr();
												SootMethod calledmethod1  = vInvExpr1.getMethod();
												Value base1 = vInvExpr1.getBase();
												PointsToSet pts1 = pta.reachingObjects((Local)base1);
//												//cg.spark returns an instance of DoublePointsToSet
//												DoublePointsToSet doublePTS = (DoublePointsToSet) pta.reachingObjects(local);
												
												Set<Type> types1 = pts1.possibleTypes();
//												System.out.println(base1 + ": types are " + types1);
												boolean threadClassflag1 = false;
												//if you want to obtain the Soot Class corresponding to each of the ref types
												for(Type type1 : types1) {
													if(type1 instanceof RefType) {
														RefType ref1 = (RefType) type1;
														SootClass sC1 = ref1.getSootClass();
														if(sC1.getName().equals(rhsclass)) {
															if(calledmethod1.getName().equals(rhsmethod)) {
																result[count] = "YES";
															}
														}
													}
												}
											}
										}
														
														
														
														
									}
								}
							}
						}
//						System.out.println(type);
					}
					
				}
			}
		}
//	if(result[count].equals("")) {
//		result[count] = "NO";
//	}
	count++;
	}
	if(queries.size()==1 && result[0].equals("NO")) {
//		result[0] = "YES";	//CHANGED
	}
	for(int i = 0; i < queries.size();i++) {
		resultString = resultString+result[i]+"\n";
//		System.out.println(result[i]);
	}
//	TODO:
//		CFG to find pred is not correct. mmap of 34 should be 23 but it is showing 34.
	
	
	
	
//	
//	wl.add(mainMethod);
//	while(!wl.isEmpty())
//	{ 
//		SootMethod currentMethod = wl.poll();
//		visitedmethod.add(currentMethod);
//		Body body = currentMethod.getActiveBody();
//		UnitGraph cfg = new BriefUnitGraph(body);
//		List<Unit> heads = cfg.getHeads();
//		Unit head = heads.get(0);
//		LinkedList<Unit> queue = new LinkedList<Unit>();
//		queue.add(head);
//		while(!queue.isEmpty()) {
//			Unit unit = queue.poll();
//			System.out.println(unit);
//			Stmt stmt = (Stmt) unit;
//			if(stmt instanceof DefinitionStmt) {
//				DefinitionStmt ds = (DefinitionStmt) stmt;
//				Value lhs = ds.getLeftOp();
//				Value rhs = ds.getRightOp();
//				if(rhs instanceof InstanceFieldRef) {System.out.println("Instancefieldref");}
//					
//				/*for each method call add to the working list Need call graph too.*/
//				/*do not add the method if it present in wl or visitedmethod list. */
//			} else if (stmt instanceof InvokeStmt) {
//				InvokeStmt invstmt = (InvokeStmt)stmt;
//				if(invstmt.getInvokeExpr() instanceof VirtualInvokeExpr) {
//					System.out.println("Virtual invoke statement");
//					
//				}
//				else if(invstmt.getInvokeExpr() instanceof SpecialInvokeExpr) {
//					System.out.println("Special invoke statement.");
//					/* ignoring the constructors */
//				}
//			} else if (stmt instanceof ReturnStmt) {
//				
//			} else {
//				System.out.println("I do not care about this statement");
//			}
//			
//			
//			List<Unit> successors = cfg.getSuccsOf(unit);
//			if(successors != null)
//				queue.addAll(successors);
//		}
//	}
//		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		

		/*************************************************************************/
		
		
		//say we want to know the runtime types of each local in Main.main
//		SootMethod mainMethod = Scene.v().getMainMethod();
//		PointsToAnalysis pta = Scene.v().getPointsToAnalysis();
		
//		for(Local local : mainMethod.getActiveBody().getLocals()) {
//			PointsToSet pts = pta.reachingObjects(local);
//			//cg.spark returns an instance of DoublePointsToSet
//			DoublePointsToSet doublePTS = (DoublePointsToSet) pta.reachingObjects(local);
//			
//			Set<Type> types = pts.possibleTypes();
//			System.out.println(local + ": types are " + types);
//			
//			//if you want to obtain the Soot Class corresponding to each of the ref types
//			for(Type type : types) {
//				if(type instanceof RefType) {
//					RefType ref = (RefType) type;
//					SootClass sC = ref.getSootClass();
//				}
//				System.out.println(type);
//			}
//			System.out.println();
//		}
		/*************************************************************************/
		
		
//		//now lets try to determine if two locals, say t1 and t2 are aliases
//
//		Local t1 = null;
//		Local t2 = null;
//		for(Local local : mainMethod.getActiveBody().getLocals()) {
//			if(local.getName().equals("t1"))
//				t1 = local;
//			else if(local.getName().equals("t2"))
//				t2 = local;
//			else 
//				continue;
//		}
//		
//
//		PointsToSet pts_t1 = pta.reachingObjects(t1);
//		PointsToSet pts_t2 = pta.reachingObjects(t2);
//		
//		boolean isAlias = pts_t1.hasNonEmptyIntersection(pts_t2);
//		System.out.println(isAlias);

		/*************************************************************************/
		
		
//		//interprocedural
//		//for the attached test case, lets check if t1.b and t2.b are the same object
//		//(it indeed should be, since it is the object used for synchronization)
//		SootMethod bRun = Scene.v().getSootClass("B").getMethodByName("run");
//		SootMethod cRun = Scene.v().getSootClass("C").getMethodByName("run");
//		
//		Local t1b = null;
//		Local t2b = null;
//		
//		for(Local local : bRun.getActiveBody().getLocals()) {
//			if (local.getName().equals("temp$0")) {
//				t1b = local;
//				break;
//			}
//		}
//		
//		for(Local local : cRun.getActiveBody().getLocals()) {
//			if (local.getName().equals("temp$0")) {
//				t2b = local;
//				break;
//			}
//		}
//		
//		PointsToSet pts_t1b = pta.reachingObjects(t1b);
//		PointsToSet pts_t2b = pta.reachingObjects(t2b);
//		System.out.println(pts_t1b.hasNonEmptyIntersection(pts_t2b));

		/*************************************************************************/

	}

}
