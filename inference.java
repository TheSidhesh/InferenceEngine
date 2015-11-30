import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Set;


public class inference 
{

	static class Term
	{
		public String name;
		public int noofvar;
		public ArrayList<String> var = new ArrayList<String>();
		public Term()
		{
			
		}
		public Term(Term term)
		{
			this.name=term.name;
			this.noofvar=term.noofvar;
			this.var.addAll(term.var);
		}	
	}
	static class Queue
	{
		public Clause clause;
		int index;
		public Queue()
		{
			
		}
		public Queue(Clause clause,int index)
		{
			this.clause=clause;
			this.index=index;
		}
	}
	static class Clause
	{
		ArrayList<String> variables = new ArrayList<String>();
		ArrayList<Term> antecedents = new ArrayList<Term>();
		String implied;
		HashMap<String,String> substitution = new HashMap<String,String>();
		public Clause()
		{
			
		}
		public Clause(Clause clause)
		{
			this.variables.addAll(clause.variables);
			for(Term term : clause.antecedents)
			{
				this.antecedents.add(new Term(term));
			}
			this.implied=clause.implied;
			for(String var : clause.substitution.keySet())
			{
				this.substitution.put(var, clause.substitution.get(var));
			}
			
		}
	}
	static class Tempmap
	{
		ArrayList<String> variable = new ArrayList<String>();
		ArrayList<String> cons = new ArrayList<String>();
	}

	static HashMap<String,ArrayList<Clause>> clause;
	static HashMap<String,ArrayList<Term>> processed;
	static HashMap<String, ArrayList<Term>> facts;
	static ArrayList<String> queries;
	static ArrayList<String> kb;
	static ArrayList<String> factsstring;
	static ArrayList<String> rulesstring;
	static int noofqueries,kblines;
	
	
	
	static String splitword(String word,ArrayList<String> vars)
	{
		String[] split = word.split("\\(");
		String w;
		String[] q =split[1].split("\\)");
		
		
		String[] v = q[0].split(",");
		for(int i=0;i<v.length;i++)
		{
			vars.add(v[i]);
		}
		w=split[0];
		return w;
	}
	static void splitclause(String word)
	{
		String[] split = word.split(" => ");
		String[] clauses = split[0].split(" \\^ ");
		String clausename,tempname;
		ArrayList<String> vars = new ArrayList<String>();
		
		Clause c = new Clause();
	
		clausename=splitword(split[1],vars);
		
		for(int i=0;i<vars.size();i++)
		{
			c.variables.add(vars.get(i));
		}
		
		for(int i=0;i<clauses.length;i++)
		{
			Term t = new Term();
			ArrayList<String> clausevar = new ArrayList<String>();
			tempname=splitword(clauses[i],clausevar);
			t.noofvar=clausevar.size();
			t.name=tempname;
			for(int j=0;j<clausevar.size();j++)
			{
				t.var.add(clausevar.get(j));
			}
			c.antecedents.add(t);	
		}
		c.implied=clausename;
		for(int i=0;i<c.antecedents.size();i++)
		{
			Term t = new Term();
			t=c.antecedents.get(i);
			for(int k=0;k<t.noofvar;k++)
			{
				if(!isAconstant(t.var.get(k)))
				{
					if(!c.substitution.containsKey(t.var.get(k)))
					{
						c.substitution.put(t.var.get(k), null);
					}
				}
				
			}
		}
		if(clause.containsKey(clausename) !=true)
		{
			ArrayList<Clause> list = new ArrayList<Clause>();
			list.add(c);
		    clause.put(clausename, list);	
		}
		else
		{
			ArrayList<Clause> list = new ArrayList<Clause>();
			list=clause.get(clausename);
			list.add(c);	
		}		
	}
	static void addtoprocessed(Term term)
	{
		
		if(processed.containsKey(term.name))
		{
			ArrayList<Term> list = new ArrayList<Term>();
			list=processed.get(term.name);
			list.add(term);
		}
		else
		{
			ArrayList<Term> list = new ArrayList<Term>();
			list.add(term);
			processed.put(term.name, list);
		}
	}
	static void addtofacts(Term term)
	{
		
		if(facts.containsKey(term.name))
		{
			ArrayList<Term> list = new ArrayList<Term>();
			list=facts.get(term.name);
			list.add(term);
		}
		else
		{
			ArrayList<Term> list = new ArrayList<Term>();
			list.add(term);
			facts.put(term.name, list);
		}
	}
	
	static void addfacts(String l)
	{
		Term term = new Term();
		ArrayList<String> cons = new ArrayList<String>();
		String predicate = splitword(l,cons);
		term.name = predicate;
		term.noofvar=cons.size();
		term.var.addAll(cons);
		if(facts.containsKey(predicate))
		{
			ArrayList<Term> list = new ArrayList<Term>();
			list=facts.get(predicate);
			list.add(term);
		}
		else
		{
			ArrayList<Term> list = new ArrayList<Term>();
			list.add(term);
			facts.put(predicate, list);
		}
		
	}
	
	static void makekb()
	{
		int i;
		String l;
		for(i=0;i<kblines;i++)
		{
			if(!kb.get(i).contains("=>"))
			{
				l = kb.get(i);
				if(!factsstring.contains(l))
				{
					addfacts(l);
					factsstring.add(l);
				}
							
			}
			else
			{
				l = kb.get(i);
				if(!rulesstring.contains(l))
				{
					splitclause(l);
					rulesstring.add(l);
				}
				
			}
		}
	}

	static boolean isAconstant(String l)
	{
		if(Character.isUpperCase(l.charAt(0)))
		{
			return true;
		}
		return false;
	}
	static boolean inprocessed(Term term)
	{
		if(processed.containsKey(term.name))
		{
			ArrayList<Term> list = new ArrayList<Term>();
			list=processed.get(term.name);
			for(int i=0;i<list.size();i++)
			{
				Term t = list.get(i);
				boolean found = true;
				for(int k=0;k<t.noofvar;k++)
				{	
					if(isAconstant(t.var.get(k)) || isAconstant(term.var.get(k)))
					{
						if(!t.var.get(k).equals(term.var.get(k)))
						{
							found = false;
							break;
						}
					}
				}
				if(found)
				{
					return true;
				}
			}
			return false;
			
		}
		else
		{
			return false;
		}	
	}
	
	static void checkinfacts(ArrayList<Term> factssubstitute,Term goal)
	{
		int flag=0;
		if(facts.containsKey(goal.name))
		{
			ArrayList<Term> list = new ArrayList<Term>();
			list=facts.get(goal.name);
			for(int i=0;i<list.size();i++)
			{
				flag=0;
				Term t = new Term();
				t = list.get(i);
				for(int k=0;k<goal.noofvar;k++)
				{
					if(isAconstant(goal.var.get(k)))
					{
						if(t.var.get(k).equals(goal.var.get(k)))
						{
							flag=1;
						}
						else
						{
							flag=0;
							break;
						}
					}
					else
					{
						flag=1;
					}
				}
				if(flag==1)
				{
					factssubstitute.add(t);
				}
				
			}
		}
	}
	static boolean canbeused(Term goal,Clause clause)
	{
		for(int i=0;i<goal.noofvar;i++)
		{
			if(isAconstant(goal.var.get(i)))
			{
				if(isAconstant(clause.variables.get(i)))
				{
					if(!goal.var.get(i).equals(clause.variables.get(i)))
					{
						return false;
					}
				}
				
			}
		}
		return true;
	}
	
	static boolean mapforright(Clause clause, Term goal)
	{
		HashMap<String,String> map = new HashMap<String,String>();
		for(int i=0;i<goal.noofvar;i++)
		{
			if(!isAconstant(goal.var.get(i)))
			{
				if(!map.containsKey(goal.var.get(i)))
				{
					map.put(goal.var.get(i), clause.variables.get(i));
				}
				else
				{
					String replace = clause.variables.get(i);
					String replaceto = map.get(goal.var.get(i));
					if(isAconstant(replace) )
					{
						map.put(goal.var.get(i),replace);
						continue;
					}
					for(int j=0;j<clause.variables.size();j++)
					{
						if(clause.variables.get(j).equals(replace))
						{
							clause.variables.remove(j);
							clause.variables.add(j,replaceto);
						}
					}
					for(Term t : clause.antecedents)
					{
						for(int k=0;k<t.noofvar;k++)
						{
							if(t.var.get(k).equals(replace))
							{
								t.var.remove(k);
								t.var.add(k,replaceto);
							}
						}		
					}
				}
			}
		}
		return true;
	}
	
	static boolean unifyforright(Clause clause,Term goal)
	{
		boolean returnmap;
		returnmap=mapforright(clause,goal);
		for(int i=0;i<clause.variables.size();i++)
		{
			if(!isAconstant(clause.variables.get(i)))
			{
				if(isAconstant(goal.var.get(i)))
				{
					String get=clause.substitution.get(clause.variables.get(i));
					if(get==null || get.equals(goal.var.get(i)))
					{
						clause.substitution.put(clause.variables.get(i), goal.var.get(i));
					}
					else
					{
						return false;
					}
				}
			}		
		}
		
		for(int i=0;i<clause.variables.size();i++)
		{
			if(!isAconstant(clause.variables.get(i)))
			{
				if(clause.substitution.get(clause.variables.get(i))!=null)
				{
					String temp=clause.variables.get(i);
					clause.variables.remove(i);
					clause.variables.add(i, clause.substitution.get(temp));
				}
			}
		}
						
		for(int i=0;i<clause.antecedents.size();i++)
		{
			Term t = new Term();
			t=clause.antecedents.get(i);
			for(int j=0;j<t.noofvar;j++)
			{
				if(!isAconstant(t.var.get(j)))
				{
					if(clause.substitution.get(t.var.get(j))!=null)
					{
						String temp=t.var.get(j);
						t.var.remove(j);
						t.var.add(j, clause.substitution.get(temp));
					}
				}	
			}
		}		
		return true;
	}
	
	static boolean mapforleft(Clause c1,Term fact,int index)
	{
		HashMap<String,String> map = new HashMap<String,String>();
		Term t = new Term();
		t = c1.antecedents.get(index);
		for(int i=0;i<fact.noofvar;i++)
		{
			if(!isAconstant(fact.var.get(i)))
			{
				if(!map.containsKey(fact.var.get(i)))
				{
					map.put(fact.var.get(i), t.var.get(i));
				}
				else
				{
					String replace = t.var.get(i);
					String replaceto = map.get(fact.var.get(i));
					if(isAconstant(replace) )//&& !replace.equals(replaceto))
					{
						map.put(fact.var.get(i),replace);
						continue;
						//return false;
					}
					for(int j=0;j<c1.variables.size();j++)
					{
						if(c1.variables.get(j).equals(replace))
						{
							c1.variables.remove(j);
							c1.variables.add(j,replaceto);
						}
					}
					for(int j=0;j<t.noofvar;j++)
					{
						if(t.var.get(j).equals(replace))
						{
							t.var.remove(j);
							t.var.add(j,replaceto);
						}
					}
					for(int j=index+1; j< c1.antecedents.size();j++)
					{
						Term t1 = c1.antecedents.get(j);
						for(int k=0;k<t1.noofvar;k++)
						{
							if(t1.var.get(k).equals(replace))
							{
								t1.var.remove(k);
								t1.var.add(k,replaceto);
							}
						}		
					}
				}
			}
		}
		return true;
	}
	static boolean substituteforleft(Clause c1,Term fact,int index)
	{
		boolean returnmap;
		returnmap=mapforleft(c1,fact,index);
		Term t = new Term();
		t=c1.antecedents.get(index);
		
		for(int i=0;i<t.noofvar;i++)
		{
			if(!isAconstant(t.var.get(i)))
			{
				if(isAconstant(fact.var.get(i)))
				{
					String get = c1.substitution.get(t.var.get(i));
					if(get==null || get.equals(fact.var.get(i)))
					{
						c1.substitution.put(t.var.get(i), fact.var.get(i));
						t.var.remove(i);
						t.var.add(i,fact.var.get(i));
					}
					else
					{
						return false;
					}
					
				}
			}
		}
		
		for(int i=index+1;i<c1.antecedents.size();i++)
		{
			Term t1 = new Term();
			t1=c1.antecedents.get(i);
			for(int k=0;k<t1.noofvar;k++)
			{
				if(!isAconstant(t1.var.get(k)))
				{
					if(c1.substitution.get(t1.var.get(k))!=null)
					{
						String temp = t1.var.get(k);
						t1.var.remove(k);
						t1.var.add(k, c1.substitution.get(temp));
					}
				}
			}	
		}
		for(int i=0;i<c1.variables.size();i++)
		{
			if(!isAconstant(c1.variables.get(i)))
			{
				if(c1.substitution.get(c1.variables.get(i))!=null)
				{
					String temp = c1.variables.get(i);
					c1.variables.remove(i);
					c1.variables.add(i, c1.substitution.get(temp));
				}
			}
			
		}
		return true;
	}
	
	static ArrayList<Term> bcor(Term goal)
	{
		boolean value;
		ArrayList<Term> factssubstitute = new ArrayList<Term>();
		ArrayList<Term> substitute = new ArrayList<Term>();
		ArrayList<Term> newfacts = new ArrayList<Term>();
		HashMap<String,ArrayList<Term>> localprocessed = new HashMap<String,ArrayList<Term>>(processed);
		
		checkinfacts(newfacts,goal);
		factssubstitute.addAll(newfacts);
		if(inprocessed(goal))
		{
			return factssubstitute;	
		}
		
		addtoprocessed(goal);
		ArrayList<Clause> c = new ArrayList<Clause>();
		if(clause.containsKey(goal.name))
		{
			c.addAll(clause.get(goal.name));	
			for(int i=0;i<c.size();i++)
			{
				Clause clause = new Clause(c.get(i));
				if(canbeused(goal,clause))
				{
					value = unifyforright(clause,goal);
					if(value==false)
					{
						continue;
					}
					substitute=bcand(clause);
					if(substitute!=null)
					{
						factssubstitute.addAll(substitute);
					}
				}
			}
		}
		processed=localprocessed;
		if(factssubstitute.isEmpty())
		{
			return null;
		}
		
		return factssubstitute;
	}
	
	static ArrayList<Term> bcand(Clause clause)
	{
		ArrayList<Queue> queue = new ArrayList<Queue>();
		ArrayList<Term> factssubstitute = new ArrayList<Term>();
		boolean value;
		Queue q = new Queue(clause,-1);
		queue.add(q);
		while(!queue.isEmpty())
		{
			Queue c = new Queue();
			c = queue.remove(0);
			Clause current = new Clause();
			current = c.clause;
			int currentindex = c.index;
			if(currentindex+1<current.antecedents.size())
			{
                ArrayList<Term> tempresult = bcor(current.antecedents.get(currentindex+1));
                if(tempresult == null)
                {
                    continue;
                }
                for(Term newfact: tempresult)
                {
                    Clause c1 = new Clause(current);
                    value=substituteforleft(c1,newfact,currentindex+1);
                    if(value==false)
                    {
                    	continue;
                    }
                    queue.add(new Queue(c1,currentindex+1));   
                }
            }
			else
			{
				Term t2 = new Term();
				t2.name=current.implied;
				t2.noofvar=current.variables.size();
				t2.var.addAll(current.variables);
				factssubstitute.add(t2);
			}
				
		}
		if(factssubstitute.isEmpty())
		{
			return null;
		}
		return factssubstitute;
	}
	
	
	static void backwardchaining() throws FileNotFoundException, IOException
	{
		File file = new File("output.txt");
		
		FileWriter fw1 = new FileWriter(file,false);
		fw1.close();
		for(int i=0;i<queries.size();i++)
		{
			String predicate;
			
			Term query = new Term();
			processed.clear();
			ArrayList<Term> factssubstitute = new ArrayList<Term>();
			ArrayList<String> constants = new ArrayList<String>();
			predicate=splitword(queries.get(i),constants);
			query.name=predicate;
			query.noofvar=constants.size();
			query.var.addAll(constants);
			try
			{
				factssubstitute=bcor(query);
				if(factssubstitute==null)
				{
					FileWriter fw = new FileWriter(file,true);
					BufferedWriter bufferedWriter = new BufferedWriter(fw);
					bufferedWriter.write("FALSE");
					bufferedWriter.newLine();
					bufferedWriter.flush();
					bufferedWriter.close();
				}
				else
				{
					addtofacts(query);
					FileWriter fw = new FileWriter(file,true);
					BufferedWriter bufferedWriter = new BufferedWriter(fw);
					bufferedWriter.write("TRUE");
					bufferedWriter.newLine();
					bufferedWriter.flush();
					bufferedWriter.close();					
				}
			}
			catch(Exception e)
			{
				FileWriter fw = new FileWriter(file,true);
				BufferedWriter bufferedWriter = new BufferedWriter(fw);
				bufferedWriter.write("FALSE");
				bufferedWriter.newLine();
				bufferedWriter.flush();
				bufferedWriter.close();
			}	
		}	
	}
	
	
	public static void main(String[] args) throws Exception
	{
		FileReader fileReader = new FileReader(args[1]);
		BufferedReader bufferedReader = new BufferedReader(fileReader);
		
		clause = new HashMap<String,ArrayList<Clause>>();
		queries = new ArrayList<String>();
		kb= new ArrayList<String>();
		factsstring = new ArrayList<String>();
		rulesstring = new ArrayList<String>();
		facts = new HashMap<String,ArrayList<Term>>();
		processed = new HashMap<String,ArrayList<Term>>();
		noofqueries = Integer.parseInt(bufferedReader.readLine());
		for(int i=0;i<noofqueries;i++)
		{
			queries.add(bufferedReader.readLine());
		}
		kblines=Integer.parseInt(bufferedReader.readLine());
		for(int i=0;i<kblines;i++)
		{
			kb.add(bufferedReader.readLine());
		}
		makekb();
		backwardchaining();
		bufferedReader.close();
	}
}
