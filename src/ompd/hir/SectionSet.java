package ompd.hir;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;
import java.util.LinkedHashMap;

import cetus.hir.*;
import cetus.analysis.LoopTools;
import cetus.analysis.RangeDomain;
import cetus.analysis.Relation;

public class SectionSet extends ArrayList<SectionSet.SECTION> implements Cloneable{

	private static final long serialVersionUID = 14L;
	public SectionSet(){
		super();
	}
	public SectionSet(SECTION section){
		super();
		this.add(section);
	}
	public SectionSet clone(){
		SectionSet tmp=new SectionSet();
		for(SECTION e:this)
			tmp.add(e.clone());
		return tmp;
	}
	public String toString(){
		String tmp="{";
		for(int i=0;i<this.size();i++){
			tmp = tmp+this.get(i).toString();
			if(i != this.size()-1)
				tmp=tmp+", ";
		}
		tmp=tmp+"}";
		return tmp;
	}
	public int get_dim_size(){
		if(this.isEmpty())
			return -1;
		return this.get(0).get_dim_size();
	}
	
	public boolean containsInfiniteElement(){
		for(SECTION sec1:this)
			if(sec1.containsInfiniteElement())
				return true;
		return false;
	}
	public boolean IsDisjoint(SectionSet other, RangeDomain rd){
		if(other==null || other.isEmpty() || this.isEmpty())
			return true;
		for(SECTION sec1:this)
			for(SECTION sec2:other)
				if(!sec1.isIndependent(sec2, rd))
					return false;
		return true;			
		
	}
	
	/* Note that unknown intersections are empty */
	public SectionSet intersectWith (SectionSet other, RangeDomain rd){
		if(other==null || other.isEmpty() || this.isEmpty())
			return new SectionSet();
		SectionSet result= new SectionSet();
		if(this.IsEqual(other, rd))
			return this.clone();
		for(SECTION sec1:this)
			for(SECTION sec2:other){
				if(sec1.isSerial() && sec2.isSerial()){
					SECTION tmp = sec1.intersectWith(sec2, rd);
					if(tmp != null && tmp.isEmpty()==false)
						result.add(tmp,rd);
				}
				else if(sec1.isSerial() && sec2.isParallel()){
					if(sec2.isSubsetOf(sec1, rd))
						result.add(sec2,rd);
				} 
				else if(sec1.isParallel() && sec2.isSerial()){
					if(sec1.isSubsetOf(sec2, rd))
						result.add(sec1,rd);
				}
				else{ // sec1.isParallel() && sec2.isParallel()
					if(sec1.isEqual(sec2, rd))
						result.add(sec1,rd);
				}	
			}
		return result;
	}
	
	public static SectionSet union (SECTION e1, SECTION e2, RangeDomain rd){
		SectionSet t = new SectionSet(e1.clone());
		t.add(e2,rd);
		return t;
	}
	public SectionSet unionWith (SectionSet other, RangeDomain rd){
		if(other==null || other.isEmpty())
			return this.clone();
		if(this.isEmpty())
			return other.clone();
		assert(this.get_dim_size()==other.get_dim_size());
		SectionSet result;
		if(this.size()>other.size()){
			result=this.clone();
			for(SECTION sec:other){
				result.add(sec,rd);
			}
		}
		else{
			result=other.clone();
			for(SECTION sec:this){
				result.add(sec,rd);
			}
		}
		return result;
	}
	
	public SectionSet unionWith_xp (SectionSet other, RangeDomain rd){
		if(other==null || other.isEmpty())
			return this.clone();
		if(this.isEmpty())
			return other.clone();
		assert(this.get_dim_size()==other.get_dim_size());
		SectionSet result;
		if(this.size()>other.size()){
			 result=this.clone();
			for(SECTION sec:other){
				result.add_xp(sec,rd);
			}
		}
		else{
			result=other.clone();
			for(SECTION sec:this){
				result.add_xp(sec,rd);
			}
		}
		return result;
	}
	
	public SectionSet subtractFrom (SectionSet other, RangeDomain rd, boolean enable_delayed_subtraction){
		if(this.isEmpty())
			return new SectionSet();
		if(other==null || other.isEmpty() )
			return this.clone();
		SectionSet result= new SectionSet();
		for(SECTION sec1:this){
			SectionSet tmp = SectionSet.subtractSetFromSection(sec1, other, rd, enable_delayed_subtraction);
			result = result.unionWith(tmp, rd);
		}
		return result;
	}
	
	
	
	public static SectionSet subtractSetFromSection(SECTION sec1, SectionSet other, RangeDomain rd, boolean enable_delayed_subtraction){

		if(sec1.isEmpty())
			return new SectionSet();
		if(other==null || other.isEmpty())
			return new SectionSet(sec1.clone());
		/*if(sec1.isRSD() && ((RSD)sec1).containsInfiniteElement())
			return new SectionSet(sec1.clone());*/
		
		SectionSet right_terms= new SectionSet();
		for(SECTION sec:other){
			if(sec.isERSD())
				continue;
			if(((RSD)sec).containsInfiniteElement())
				continue;
			if(sec.isIndependent(sec1, rd))
				continue;
			right_terms.add(sec);
				
		}
		if(right_terms.isEmpty())
			return new SectionSet(sec1.clone());

		
		if(sec1.isERSD()){
			for(int i=1;i<((ERSD)sec1).size();i++){
				RSD rsd = ((ERSD)sec1).get(i);
				//right_terms.add(rsd,rd);
				boolean add_elm = true;
				SectionSet delete = new SectionSet();
				for(SECTION s : right_terms){
					assert(s.isSerial()==true);
					assert(rsd.isSerial()==true);
					if(rsd.isSubsetOf(s, rd))
						{add_elm = false; break;}
					else if(s.isSubsetOf(rsd, rd))
						delete.add(s);
				}
				if(add_elm){
					for(SECTION s: delete)
						right_terms.remove(s);
					right_terms.add(rsd,rd);
				}	
			}
		}
		
		SectionSet set ;
		if(sec1.isERSD())
			set = new SectionSet(((ERSD)sec1).get(0).clone());
		else
			set = new SectionSet(sec1.clone());
		
		for(int i=0;i<right_terms.size();i++){
			if(set.isEmpty())
				break;
    		SectionSet tmp = set.clone();
    		for(int j=0;j<tmp.size();j++){
    			if(tmp.get(j).isIndependent(right_terms.get(i), rd))
    				continue;
    			else if(tmp.get(j).isSerial() && right_terms.get(i).isSerial()){
    				SectionSet sub = ((RSD)tmp.get(j)).subtractFrom((RSD)right_terms.get(i), rd);
        			if(sub==null)
        				continue;
        			set.remove(tmp.get(j));
        			if(sub.isEmpty())
        				break;
        			set = set.unionWith(sub, rd);	
    			}
    			else if(tmp.get(j).isSerial() && right_terms.get(i).isParallel()){
    				// do not subtract parallel from serial
    				continue;
    			}
    			else if(tmp.get(j).isParallel() && right_terms.get(i).isSerial()){
    				if(ELEMENT.IsSubsetOf(((RSD)tmp.get(j)).get(tmp.get(j).get_parallel_dim()), ((RSD)right_terms.get(i)).get(tmp.get(j).get_parallel_dim()), rd).equals(BOOLEAN.TRUE)){
    					SectionSet sub = ((RSD)tmp.get(j)).subtractFrom((RSD)right_terms.get(i), rd);
	        			if(sub==null)
	        				continue;
	        			set.remove(tmp.get(j));
	        			if(sub.isEmpty())
	        				break;
	        			set = set.unionWith(sub, rd);
    				}
    			}
    			else if(tmp.get(j).isParallel() && right_terms.get(i).isParallel()){
    				if(right_terms.get(i).get_parallel_dim()==tmp.get(j).get_parallel_dim())
    					if(ELEMENT.IsEqual(((RSD)right_terms.get(i)).get(right_terms.get(i).get_parallel_dim()), ((RSD)tmp.get(j)).get(tmp.get(j).get_parallel_dim()), rd).equals(BOOLEAN.TRUE)){
    						SectionSet sub = ((RSD)tmp.get(j)).subtractFrom((RSD)right_terms.get(i), rd);
    	        			if(sub==null)
    	        				continue;
    	        			set.remove(tmp.get(j));
    	        			if(sub.isEmpty())
    	        				break;
    	        			set = set.unionWith(sub, rd);	
    					}
    			}
    		}
    		tmp=null;
    	}
		
		if(set.isEmpty())
			return new SectionSet();
		
		if(enable_delayed_subtraction==false)
			return set;
		
		if(right_terms.size()>1){
			SectionSet tmp = right_terms.clone();
			right_terms.clear();
			for(SECTION s : tmp)
				right_terms.add(s,rd);
		}
		
		
		SectionSet res = new SectionSet();
    	for(SECTION sec:set){
    		//if(sec.isSerial())
    		//	res.add(sec);
    		//else{
    			ERSD ersd = new ERSD();
    			ersd.add(0,(RSD)sec);
        		for(int i=0;i<right_terms.size();i++){
        			SECTION tmp = ((RSD)sec).intersectWith((RSD)right_terms.get(i), rd);
            		if(tmp==null || !tmp.isEmpty())
            			ersd.add((RSD)right_terms.get(i));           		
            	}
        		if(ersd.size()==1){
        			res.add(sec);
        		}
        		else
        			res.add(ersd);
    		//}
    	}
		
    	return res;
	}
	
	public static SectionSet subtractSetFromSection(SECTION sec1, SectionSet other, RangeDomain rd){
		return SectionSet.subtractSetFromSection(sec1, other, rd, true);
	}
	public SectionSet subtractFrom_xp (SectionSet other, RangeDomain rd){
		if(this.isEmpty())
			return new SectionSet();
		if(other==null || other.isEmpty() )
			return this.clone();
		SectionSet result= new SectionSet();
		for(SECTION sec1:this){
			SectionSet tmp = SectionSet.subtractSetFromSection_xp(sec1, other, rd);
			result = result.unionWith_xp(tmp, rd);
		}
		return result;
	}
	
	public static SectionSet subtractSetFromSection_xp(SECTION sec1, SectionSet other, RangeDomain rd){
		if(sec1.isEmpty())
			return new SectionSet();
		if(other==null || other.isEmpty())
			return new SectionSet(sec1.clone());
		
		SectionSet set;
		if(sec1.isERSD())
			set = new SectionSet(((ERSD)sec1).get(0).clone());
		else
			set = new SectionSet(sec1.clone());
				
		for(int i=0;i<other.size();i++){
			if(set.isEmpty())
				break;
			RSD right_rsd = (RSD) other.get(i);
			assert(right_rsd.isParallel());
    		SectionSet tmp = set.clone();
    		for(int j=0;j<tmp.size();j++){
    			RSD tmp_rsd = (RSD) tmp.get(j);
    			if(tmp_rsd.containsInfiniteElement())
    				continue;
    			if(tmp_rsd.IsIndependent(right_rsd, rd).equals(BOOLEAN.TRUE))
    				continue;
    			if(tmp_rsd.isParallel()){ 
    				if(tmp_rsd.get_parallel_dim()!=right_rsd.get_parallel_dim())
    					continue;
    				if(!OMPDParallelForLoop.IsSimilar(tmp_rsd.get_pfor(), right_rsd.get_pfor(), rd))
    					continue;
    				if(ELEMENT.IsEqual(tmp_rsd.get(right_rsd.get_parallel_dim()), right_rsd.get(right_rsd.get_parallel_dim()), rd).equals(BOOLEAN.TRUE)){
    					RSD t = right_rsd.clone(); t.Serialize();
    					SectionSet sub = tmp_rsd.subtractFrom(t, rd);
	        			if(sub==null)
	        				continue;
	        			set.remove(tmp_rsd);
	        			if(sub.isEmpty())
	        				break;
	        			set = set.unionWith_xp(sub, rd);	
					}
    			}
    			else {//if(tmp_rsd.isSerial())
    				RSD t = right_rsd.clone(); t.Serialize();
    				SectionSet sub = tmp_rsd.subtractFrom(t, rd);
        			if(sub==null)
        				continue;
        			set.remove(tmp_rsd);
        			if(sub.isEmpty())
        				break;
        			set = set.unionWith_xp(sub, rd);
    			}

    		}
    		tmp=null;
    	}
		
		SectionSet result = new SectionSet();
		for(SECTION left: set){
			SectionSet right_terms;
			right_terms= new SectionSet();
			for(SECTION right: other){
				if(right.containsInfiniteElement())
					continue;
				if(left.isIndependent(right, rd))
    				continue;
				right_terms.add_xp(right,rd);
			}
			
			if(sec1.isERSD())
				for(int i=1;i<((ERSD)sec1).size();i++)
					right_terms.add_xp(((ERSD)sec1).get(i),rd);
			
			if(right_terms.size()==0)
				result.add(left);
			else
				result.add(new ERSD((RSD)left, right_terms));
		}
		return result;
		
	}
	
	public SectionSet subtractFromConservative_xp (SectionSet other, RangeDomain rd){
		if(this.isEmpty())
			return new SectionSet();
		if(other==null || other.isEmpty() )
			return this.clone();
		SectionSet result= new SectionSet();
		for(SECTION sec1:this){
			SectionSet tmp = SectionSet.subtractSetFromSection_xp(sec1, other, rd);
			Set<ERSD> ERSDs = new HashSet<ERSD>();
			for(SECTION e:tmp)
				if(e.isERSD())
					ERSDs.add((ERSD)e);
			for(ERSD e:ERSDs){
				tmp.remove(e);
				tmp.add(e.get(0), rd);
			}	
			result = result.unionWith_xp(tmp, rd);
		}
		return result;
	}
	
	public boolean IsEqual(SectionSet other, RangeDomain rd){
		assert(other!=null);
		if(other.isEmpty())
			if(this.isEmpty())
				return true;
			else
				return false;
		if(other.size() != this.size())
			return false;
		assert(this.get_dim_size()==other.get_dim_size());
		SectionSet tmp = (SectionSet)other.clone();
		for(SECTION sec:this){
			if(tmp.containsSECTION(sec, rd))
				tmp.remove(sec);
		}
		if(tmp.isEmpty() == false)
			return false;
		SectionSet tmp2 = (SectionSet)this.clone();
		for(SECTION sec:other){
			if(tmp2.containsSECTION(sec, rd))
				tmp2.remove(sec);
		}
		if(tmp2.isEmpty() == false)
			return false;
		return true;
	}
	public boolean IsEqual_xp(SectionSet other, RangeDomain rd){
		assert(other!=null);
		if(other.isEmpty())
			if(this.isEmpty())
				return true;
			else
				return false;
		if(other.size() != this.size())
			return false;
		assert(this.get_dim_size()==other.get_dim_size());
		SectionSet tmp = (SectionSet)other.clone();
		for(SECTION sec:this){
			if(tmp.containsSECTION_xp(sec, rd))
				tmp.remove(sec);
		}
		if(tmp.isEmpty() == false)
			return false;
		SectionSet tmp2 = (SectionSet)this.clone();
		for(SECTION sec:other){
			if(tmp2.containsSECTION_xp(sec, rd))
				tmp2.remove(sec);
		}
		if(tmp2.isEmpty() == false)
			return false;
		return true;
	}
	
	public boolean add_xp(SECTION elm, RangeDomain rd){
		//assert(elm.isRSD()==true);
		SECTION e = elm.clone();
		if(this.size()==0){
			super.add(e);
			return true;
		}
		ArrayList<SECTION> to_be_deleted=new ArrayList<SECTION>();
		
		if(e.isRSD() && ((RSD)e).containsInfiniteElement()){
			for(SECTION s:this){
				if(s.isRSD() && ((RSD)s).containsInfiniteElement()){
					if(e.isEqual(s, rd))
						return false;
				} 
				
			}	
			super.add(e);
			return true;
		}
		
		if(e.isERSD() && ((ERSD)e).get(0).containsInfiniteElement()){
			for(SECTION s:this){
				if(s.isERSD() && ((ERSD)s).get(0).containsInfiniteElement()){
					if(e.isEqual(s, rd))
						return false;
				}
				else if(s.isRSD() && ((RSD)s).containsInfiniteElement()){
					if(s.isEqual(((ERSD)e).get(0),rd))
						return false;
				}
			}
			//super.add(e);
			//return true;
		}
		
		SectionSet tmpp = new SectionSet(e);
		for(SECTION s: this){
			SectionSet tmppp = tmpp.clone();
			for(SECTION ee : tmppp){
				if(s.isRSD() && ((RSD)s).containsInfiniteElement())
					continue;
				if(		s.isRSD() && e.isRSD() && s.isIndependent(ee, rd) ||
						s.isERSD() && e.isRSD() && e.isIndependent(((SectionSet.ERSD)s).get(0), rd) ||
						s.isRSD() && e.isERSD() && s.isIndependent(((SectionSet.ERSD)e).get(0), rd) ||
						s.isERSD() && e.isERSD() && ((SectionSet.ERSD)s).get(0).IsIndependent(((SectionSet.ERSD)s).get(0), rd).equals(BOOLEAN.TRUE) ){
					SECTION sec = combine_two_independent_sections_if_neighbours_xp(s,ee,rd);
					if(sec!=null){
						to_be_deleted.add(s);
						tmpp.remove(ee);
						tmpp.add(sec);
					}
				}			
				else if(s.isSerial() && ee.isSerial()){
					if(ee.isSubsetOf(s, rd))
						tmpp.remove(ee);
					else if(s.isSubsetOf(ee, rd))
						to_be_deleted.add(s);
				}
				else if(s.isParallel() && ee.isParallel()) { 
					if(s.get_parallel_dim() == ee.get_parallel_dim() && OMPDParallelForLoop.IsSimilar(s.get_pfor(), ee.get_pfor(), rd)){
						if(s.isRSD() && ee.isRSD()){
							RSD rsd_s = (RSD)s;
							RSD rsd_ee = (RSD)ee;
							int parallel_dim = rsd_ee.get_parallel_dim();
							if(ELEMENT.IsEqual(rsd_ee.get(parallel_dim), rsd_s.get(parallel_dim), rd).equals(BOOLEAN.TRUE)){
								if(rsd_s.IsSubsetOf(rsd_ee, rd).equals(BOOLEAN.TRUE))
									to_be_deleted.add(s);
								else if(rsd_ee.IsSubsetOf(rsd_s, rd).equals(BOOLEAN.TRUE))
									tmpp.remove(ee);
								else{
									RSD intrsct = rsd_s.intersectWith(rsd_ee, rd);
									if(intrsct!=null){
										assert(!intrsct.isEmpty());
										RSD intrsct_s = intrsct.clone();
										intrsct_s.Serialize();
										SectionSet right = rsd_s.subtractFrom(intrsct_s, rd);
										SectionSet left = rsd_ee.subtractFrom(intrsct_s, rd);
										if(left!=null && right!=null){
											tmpp.remove(ee);
											to_be_deleted.add(s);
											SECTION t = intrsct;
											for(SECTION sec: left.clone()){
												SECTION tt = combine_two_independent_sections_if_neighbours(sec,t,rd);
												if(tt!=null){
													t = tt;
													left.remove(sec);
												}
											}
											for(SECTION sec: right.clone()){
												SECTION tt = combine_two_independent_sections_if_neighbours(sec,t,rd);
												if(tt!=null){
													t = tt;
													right.remove(sec);
												}
											}
											for(SECTION sec: left)
												tmpp.add(sec);
											for(SECTION sec: right)
												tmpp.add(sec);
											tmpp.add(t);
										}
										else if(left!=null){
											tmpp.remove(ee);
											SECTION t = rsd_s;
											for(SECTION sec: left.clone()){
												SECTION tt = combine_two_independent_sections_if_neighbours(sec,t,rd);
												if(tt!=null){
													t = tt;
													left.remove(sec);
												}
											}
											if(!t.isEqual(rsd_s, rd)){
												to_be_deleted.add(s);
												tmpp.add(t);
											}
											for(SECTION sec: left)
												tmpp.add(sec);
												
										}
										else if(right!=null){
											to_be_deleted.add(s);
											SECTION t = rsd_ee;
											for(SECTION sec: right.clone()){
												SECTION tt = combine_two_independent_sections_if_neighbours(sec,t,rd);
												if(tt!=null){
													t = tt;
													right.remove(sec);
												}
											}
											if(!t.isEqual(rsd_ee, rd)){
												tmpp.remove(ee);
												tmpp.add(t);
											}
											for(SECTION sec: right)
												tmpp.add(sec);
										}
									}
								}
							}
						}
						else if(s.isERSD() && ee.isRSD()){
							ERSD ersd_s = (ERSD)s;
							RSD rsd_ee = (RSD)ee;
							int parallel_dim = rsd_ee.get_parallel_dim();
							if(ELEMENT.IsEqual(ersd_s.get(0).get(parallel_dim), rsd_ee.get(parallel_dim), rd).equals(BOOLEAN.TRUE)){
								if(ersd_s.get(0).IsSubsetOf(rsd_ee, rd).equals(BOOLEAN.TRUE))
									to_be_deleted.add(s);
								else if(rsd_ee.IsSubsetOf(ersd_s, rd).equals(BOOLEAN.TRUE))
									tmpp.remove(ee);
							}						
						}
						else if(s.isRSD() && ee.isERSD()){
							RSD rsd_s = (RSD)s;
							ERSD ersd_ee = (ERSD)ee;
							int parallel_dim = ersd_ee.get_parallel_dim();
							if(ELEMENT.IsEqual(rsd_s.get(parallel_dim), ersd_ee.get(0).get(parallel_dim), rd).equals(BOOLEAN.TRUE)){
								if(ersd_ee.get(0).IsSubsetOf(rsd_s, rd).equals(BOOLEAN.TRUE))
									tmpp.remove(ee);
								else if(rsd_s.IsSubsetOf(ersd_ee, rd).equals(BOOLEAN.TRUE))
									to_be_deleted.add(s);							
							}
						}
						else{ // s.isERSD() && ee.isERSD()
							if(new SectionSet(s).containsSECTION_xp(ee, rd))
								tmpp.remove(ee);
						}
					}
				}
			}
		}
		
		for(SECTION s:to_be_deleted){
			super.remove(s);
		}
		if(tmpp.isEmpty())
			return false;
		for(SECTION ss: tmpp){
			super.add(ss);
		}
		return true;	
	}
	private SECTION combine_two_independent_sections_if_neighbours_xp(SECTION s, SECTION ee, RangeDomain rd){
		boolean IsNeighbour = s.IsNeighbour(ee, rd);
		boolean both_parallel = s.isParallel() && ee.isParallel();
		boolean both_serial = s.isSerial() && ee.isSerial();
		if(IsNeighbour && (both_parallel || both_serial)){
			int s_elm, ee_elm;
			boolean proceed = false;
			if(both_parallel){
				s_elm = s.get_parallel_dim();
				ee_elm = ee.get_parallel_dim();
				if(s_elm==ee_elm){
					if(s.isRSD() && ee.isRSD() ){
						if(ELEMENT.IsEqual(((RSD)s).get(s_elm), ((RSD)ee).get(ee_elm), rd).equals(BOOLEAN.TRUE) && OMPDParallelForLoop.IsSimilar(s.get_pfor(), ee.get_pfor(), rd))
							proceed = true;
					}
					else if(s.isRSD() && ee.isERSD()){
						if(ELEMENT.IsEqual(((RSD)s).get(s_elm), ((ERSD)ee).get(0).get(ee_elm), rd).equals(BOOLEAN.TRUE) && OMPDParallelForLoop.IsSimilar(s.get_pfor(), ee.get_pfor(), rd))
							proceed = true;
					}
					else if(s.isERSD() && ee.isRSD()){
						if(ELEMENT.IsEqual(((ERSD)s).get(0).get(s_elm), ((RSD)ee).get(ee_elm), rd).equals(BOOLEAN.TRUE) && OMPDParallelForLoop.IsSimilar(s.get_pfor(), ee.get_pfor(), rd))
							proceed = true;
					}
					else{ // both are ERSD
						if(ELEMENT.IsEqual(((ERSD)s).get(0).get(s_elm), ((ERSD)ee).get(0).get(ee_elm), rd).equals(BOOLEAN.TRUE) && OMPDParallelForLoop.IsSimilar(s.get_pfor(), ee.get_pfor(), rd))
							proceed = true;
					}
				}
			}
			else
				proceed = true;
			if(proceed){
				if(s.isRSD() && ee.isRSD()){
					RSD rsd_s = (RSD)s;
					RSD rsd_ee = (RSD)ee;
					RSD sec = rsd_ee.unionWith(rsd_s, rd);
					return sec;
				}
				else if(s.isRSD() && ee.isERSD()){
					RSD rsd_s = (RSD)s;
					RSD rsd_ee = ((ERSD)ee).get(0);
					RSD sec = rsd_ee.unionWith(rsd_s, rd);
					if(sec!=null){
						ERSD t = (ERSD)ee.clone();
						t.remove(0);
						t.add(0, sec);
						return t;
					} 
				}
				else if(s.isERSD() && ee.isRSD()){
					RSD rsd_s = ((ERSD)s).get(0);
					RSD rsd_ee = (RSD)ee;
					RSD sec = rsd_ee.unionWith(rsd_s, rd);
					if(sec!=null){
						ERSD t = (ERSD)s.clone();
						t.remove(0);
						t.add(0, sec);
						return t;
					}
				}
				else{
					// ignore this case for now
				}
			}
			return null;
		}
		return null;
	}
	
	public boolean add(SECTION elm, RangeDomain rd){
		SECTION e = elm.clone();
		if(this.size()==0){
			super.add(e);
			return true;
		}
		ArrayList<SECTION> to_be_deleted=new ArrayList<SECTION>();
		
		if(e.isRSD() && ((RSD)e).containsInfiniteElement()){
			for(SECTION s:this){
				if(s.isRSD() && ((RSD)s).containsInfiniteElement()){
					if(e.isEqual(s, rd))
						return false;
				} 
				
			}	
			super.add(e);
			return true;
		}
		
		if(e.isERSD() && ((ERSD)e).get(0).containsInfiniteElement()){
			for(SECTION s:this){
				if(s.isERSD() && ((ERSD)s).get(0).containsInfiniteElement()){
					if(e.isEqual(s, rd))
						return false;
				}
				else if(s.isRSD() && ((RSD)s).containsInfiniteElement()){
					if(s.isEqual(((ERSD)e).get(0),rd))
						return false;
				}
			}
			//super.add(e);
			//return true;
		}
		
		SectionSet tmpp = new SectionSet(e);
		for(SECTION s: this){
			if(tmpp.isEmpty()) break;
			SectionSet tmppp = tmpp.clone();
			for(SECTION ee : tmppp){
				if(s.isRSD() && ((RSD)s).containsInfiniteElement())
					continue;
				if(s.isIndependent(ee, rd)){
					SECTION sec = combine_two_independent_sections_if_neighbours(s,ee,rd);
					if(sec!=null){
						to_be_deleted.add(s);
						tmpp.remove(ee);
						tmpp.add(sec);
					}
				}
				else if(s.isSerial() && ee.isSerial()){
					if(ee.isSubsetOf(s, rd))
						tmpp.remove(ee);
					else if(s.isSubsetOf(ee, rd))
						to_be_deleted.add(s);
					else{
						if(s.isRSD() && ee.isRSD()){
							RSD rsd_s = (RSD)s;
							RSD rsd_ee = (RSD)ee;
							RSD intrsct = rsd_s.intersectWith(rsd_ee, rd);
							if(intrsct!=null){
								assert(!intrsct.isEmpty());
								SectionSet right = rsd_s.subtractFrom(intrsct, rd);
								SectionSet left = rsd_ee.subtractFrom(intrsct, rd);
								if(left!=null && right!=null){
									tmpp.remove(ee);
									to_be_deleted.add(s);
									SECTION t = intrsct;
									for(SECTION sec: left.clone()){
										SECTION tt = combine_two_independent_sections_if_neighbours(sec,t,rd);
										if(tt!=null){
											t = tt;
											left.remove(sec);
										}
									}
									for(SECTION sec: right.clone()){
										SECTION tt = combine_two_independent_sections_if_neighbours(sec,t,rd);
										if(tt!=null){
											t = tt;
											right.remove(sec);
										}
									}
									for(SECTION sec: left)
										tmpp.add(sec);
									for(SECTION sec: right)
										tmpp.add(sec);
									tmpp.add(t);
								}
								else if(left!=null){
									tmpp.remove(ee);
									SECTION t = rsd_s;
									for(SECTION sec: left.clone()){
										SECTION tt = combine_two_independent_sections_if_neighbours(sec,t,rd);
										if(tt!=null){
											t = tt;
											left.remove(sec);
										}
									}
									if(!t.isEqual(rsd_s, rd)){
										to_be_deleted.add(s);
										tmpp.add(t);
									}
									for(SECTION sec: left)
										tmpp.add(sec);
										
								}
								else if(right!=null){
									to_be_deleted.add(s);
									SECTION t = rsd_ee;
									for(SECTION sec: right.clone()){
										SECTION tt = combine_two_independent_sections_if_neighbours(sec,t,rd);
										if(tt!=null){
											t = tt;
											right.remove(sec);
										}
									}
									if(!t.isEqual(rsd_ee, rd)){
										tmpp.remove(ee);
										tmpp.add(t);
									}
									for(SECTION sec: right)
										tmpp.add(sec);
								}	
							}
						}
					}
				}
				else if(s.isSerial() && ee.isParallel()){
					if(ee.isSubsetOf(s, rd))
						tmpp.remove(ee);
					else if(s.isRSD() && ee.isRSD()){
						RSD rsd_s = (RSD)s;
						RSD rsd_ee = (RSD)ee;
						int parallel_dim = rsd_ee.get_parallel_dim();
						if(ELEMENT.IsSubsetOf(rsd_ee.get(parallel_dim), rsd_s.get(parallel_dim), rd).equals(BOOLEAN.TRUE)){
							RSD intrsct = rsd_s.intersectWith(rsd_ee, rd);
							if(intrsct!=null){
								assert(!intrsct.isEmpty());
								RSD intrsct_s = intrsct.clone();
								intrsct_s.Serialize();
								SectionSet left = rsd_ee.subtractFrom(intrsct_s, rd);
								if(left!=null){
									tmpp.remove(ee);
									for(SECTION sec: left)
										tmpp.add(sec);	
								}
							}
						}	
					}
				}
				else if(s.isParallel() && ee.isSerial()){
					if(s.isSubsetOf(ee, rd)){
						to_be_deleted.add(s);
					}
					else if(s.isRSD() && ee.isRSD()){
						RSD rsd_s = (RSD)s;
						RSD rsd_ee = (RSD)ee;
						int parallel_dim = rsd_s.get_parallel_dim();
						if(ELEMENT.IsSubsetOf(rsd_s.get(parallel_dim), rsd_ee.get(parallel_dim), rd).equals(BOOLEAN.TRUE)){
							RSD intrsct = rsd_s.intersectWith(rsd_ee, rd);
							if(intrsct!=null){
								assert(!intrsct.isEmpty());
								RSD intrsct_s = intrsct.clone();
								intrsct_s.Serialize();
								SectionSet left = rsd_s.subtractFrom(intrsct_s, rd);
								if(left!=null){
									to_be_deleted.add(s);
									for(SECTION sec: left)
										tmpp.add(sec);	
								}
							}
						}	
					}
				}
				else { // s.isParallel() && ee.isParallel()
					if(s.get_parallel_dim() == ee.get_parallel_dim() /*&& OMPDParallelForLoop.IsSimilar(s.get_pfor(), ee.get_pfor(), rd)*/){
						if(s.isRSD() && ee.isRSD()){
							RSD rsd_s = (RSD)s;
							RSD rsd_ee = (RSD)ee;
							int parallel_dim = rsd_ee.get_parallel_dim();
							if(ELEMENT.IsEqual(rsd_ee.get(parallel_dim), rsd_s.get(parallel_dim), rd).equals(BOOLEAN.TRUE)){
								if(rsd_s.IsSubsetOf(rsd_ee, rd).equals(BOOLEAN.TRUE))
									to_be_deleted.add(s);
								else if(rsd_ee.IsSubsetOf(rsd_s, rd).equals(BOOLEAN.TRUE))
									tmpp.remove(ee);
								else{
									RSD intrsct = rsd_s.intersectWith(rsd_ee, rd);
									if(intrsct!=null){
										assert(!intrsct.isEmpty());
										RSD intrsct_s = intrsct.clone();
										intrsct_s.Serialize();
										SectionSet right = rsd_s.subtractFrom(intrsct_s, rd);
										SectionSet left = rsd_ee.subtractFrom(intrsct_s, rd);
										if(left!=null && right!=null){
											tmpp.remove(ee);
											to_be_deleted.add(s);
											SECTION t = intrsct;
											for(SECTION sec: left.clone()){
												SECTION tt = combine_two_independent_sections_if_neighbours(sec,t,rd);
												if(tt!=null){
													t = tt;
													left.remove(sec);
												}
											}
											for(SECTION sec: right.clone()){
												SECTION tt = combine_two_independent_sections_if_neighbours(sec,t,rd);
												if(tt!=null){
													t = tt;
													right.remove(sec);
												}
											}
											for(SECTION sec: left)
												tmpp.add(sec);
											for(SECTION sec: right)
												tmpp.add(sec);
											tmpp.add(t);
										}
										else if(left!=null){
											tmpp.remove(ee);
											SECTION t = rsd_s;
											for(SECTION sec: left.clone()){
												SECTION tt = combine_two_independent_sections_if_neighbours(sec,t,rd);
												if(tt!=null){
													t = tt;
													left.remove(sec);
												}
											}
											if(!t.isEqual(rsd_s, rd)){
												to_be_deleted.add(s);
												tmpp.add(t);
											}
											for(SECTION sec: left)
												tmpp.add(sec);
												
										}
										else if(right!=null){
											to_be_deleted.add(s);
											SECTION t = rsd_ee;
											for(SECTION sec: right.clone()){
												SECTION tt = combine_two_independent_sections_if_neighbours(sec,t,rd);
												if(tt!=null){
													t = tt;
													right.remove(sec);
												}
											}
											if(!t.isEqual(rsd_ee, rd)){
												tmpp.remove(ee);
												tmpp.add(t);
											}
											for(SECTION sec: right)
												tmpp.add(sec);
										}
									}
								}
								
							}
						}
						else if(s.isERSD() && ee.isERSD()){
							ERSD ersd_s = (ERSD)s;
							ERSD ersd_ee = (ERSD)ee;
							int parallel_dim = ersd_ee.get_parallel_dim();
							if(ELEMENT.IsEqual(ersd_s.get(0).get(parallel_dim), ersd_ee.get(0).get(parallel_dim), rd).equals(BOOLEAN.TRUE)){
								if(s.isSubsetOf(ee, rd))
									to_be_deleted.add(s);
								else if(ee.isSubsetOf(s, rd))
									tmpp.remove(ee);
							}
						}
						else if(s.isRSD() && ee.isERSD()){
							RSD rsd_s = (RSD)s;
							ERSD ersd_ee = (ERSD)ee;
							int parallel_dim = ersd_ee.get_parallel_dim();
							if(ELEMENT.IsEqual(rsd_s.get(parallel_dim), ersd_ee.get(0).get(parallel_dim), rd).equals(BOOLEAN.TRUE)){
								if(ersd_ee.IsSubsetOf(rsd_s, rd).equals(BOOLEAN.TRUE))
									tmpp.remove(ee);
								else if(rsd_s.IsSubsetOf(ersd_ee, rd).equals(BOOLEAN.TRUE))
									to_be_deleted.add(s);
							}
						}
						else{ //s.isERSD() && ee.isRSD()
							ERSD ersd_s = (ERSD)s;
							RSD rsd_ee = (RSD)ee;
							int parallel_dim = rsd_ee.get_parallel_dim();
							if(ELEMENT.IsEqual(ersd_s.get(0).get(parallel_dim), rsd_ee.get(parallel_dim), rd).equals(BOOLEAN.TRUE)){
								if(ersd_s.IsSubsetOf(rsd_ee, rd).equals(BOOLEAN.TRUE))
									to_be_deleted.add(s);
								else if(rsd_ee.IsSubsetOf(ersd_s, rd).equals(BOOLEAN.TRUE))
									tmpp.remove(ee);
							}
						}
					}
				}
			}
		}
		
		for(SECTION s:to_be_deleted){
			super.remove(s);
		}
		if(tmpp.isEmpty())
			return false;
		for(SECTION ss: tmpp){
			super.add(ss);
		}
		return true;
		
	}

	private SECTION combine_two_independent_sections_if_neighbours(SECTION s, SECTION ee, RangeDomain rd){			
		boolean IsNeighbour = s.IsNeighbour(ee, rd);
		boolean both_parallel = s.isParallel() && ee.isParallel();
		boolean both_serial = s.isSerial() && ee.isSerial();
		if(IsNeighbour && (both_parallel || both_serial)){
			boolean proceed = false;
			if(both_parallel){
				if(OMPDTools.do_both_have_same_partitioned_dimension(s, ee, rd))
					proceed=true;
			}
			else
				proceed = true;
			if(proceed){
				if(s.isRSD() && ee.isRSD()){
					RSD rsd_s = (RSD)s;
					RSD rsd_ee = (RSD)ee;
					RSD sec = rsd_ee.unionWith(rsd_s, rd);
					return sec;
				}
				else if(s.isRSD() && ee.isERSD()){
					RSD rsd_s = (RSD)s;
					RSD rsd_ee = ((ERSD)ee).get(0);
					RSD sec = rsd_ee.unionWith(rsd_s, rd);
					if(sec!=null){
						ERSD t = (ERSD)ee.clone();
						t.remove(0);
						t.add(0, sec);
						return t;
					} 
					else return null;
				}
				else if(s.isERSD() && ee.isRSD()){
					RSD rsd_s = ((ERSD)s).get(0);
					RSD rsd_ee = (RSD)ee;
					RSD sec = rsd_ee.unionWith(rsd_s, rd);
					if(sec!=null){
						ERSD t = (ERSD)s.clone();
						t.remove(0);
						t.add(0, sec);
						return t;
					}
					else return null;
				}
				else{
					/*
					RSD rsd_s = ((ERSD)s).get(0);
					RSD rsd_ee = ((ERSD)ee).get(0);
					RSD sec = rsd_ee.unionWith(rsd_s, rd);
					if(sec!=null){
						ERSD t = (ERSD)s.clone();
						t.remove(0);
						t.add(0, sec);
						for(int j=1;j<((ERSD)ee).size();j++)
							t.add(((ERSD)ee).get(j));
						return t;
					}
					else return null;
					*/
					return null; // ignore this case for now
				}
			}
			else return null;
		}
		else return null;
	}
	
	/**returns true if there is any SECTION in this set that is subsume SECTION e*/
	public boolean has(SECTION e, RangeDomain rd){
		assert(e!=null);
	    if(e.isEmpty())
	    	return true;
		if(this.isEmpty())
			return false;
		for(int i=0;i<this.size();i++){
			if(e.isSubsetOf(this.get(i), rd)){
				boolean both_parallel = e.isParallel() && this.get(i).isParallel();
				boolean both_serial = e.isSerial() && this.get(i).isSerial();
				if((both_parallel && e.get_parallel_dim()==this.get(i).get_parallel_dim()) || both_serial)
					return true; 
			}
		}
		return false;
	}
	
	/**returns true if there is one SECTION that is exactly SECTION e*/
	public boolean containsSECTION(SECTION e, RangeDomain rd){
		assert(e!=null);
	    if(e.isEmpty())
	    	return true;
		if(this.isEmpty())
			return false;
		for(int i=0;i<this.size();i++){
			if(e.isEqual(this.get(i), rd)){
				boolean both_parallel = e.isParallel() && this.get(i).isParallel();
				boolean both_serial = e.isSerial() && this.get(i).isSerial();
				if((both_parallel && e.get_parallel_dim()==this.get(i).get_parallel_dim()) || both_serial)
					return true;
			}
		}
		return false;
	}
	
	private boolean containsSECTION_xp(SECTION e, RangeDomain rd){
		assert(e!=null);
	    if(e.isEmpty())
	    	return true;
		if(this.isEmpty())
			return false;
		for(int i=0;i<this.size();i++){
			if(e.isRSD() && this.get(i).isRSD()){
				boolean both_parallel = e.isParallel() && this.get(i).isParallel();
				boolean both_serial = e.isSerial() && this.get(i).isSerial();
				if((both_parallel && e.get_parallel_dim()==this.get(i).get_parallel_dim() && OMPDParallelForLoop.IsSimilar(this.get(i).get_pfor(), e.get_pfor(), rd)) || both_serial){
					if(e.isEqual(this.get(i), rd))
						return true;
				}
			}
			else if(e.isERSD() && this.get(i).isERSD()){
				ERSD d1 = (ERSD)e;
				ERSD d2 = (ERSD)this.get(i);
				if(d1.size()!=d2.size())
					continue;
				boolean both_parallel = d1.get(0).isParallel() && d2.get(0).isParallel();
				boolean both_serial = d1.get(0).isSerial() && d2.get(0).isSerial();
				if((both_parallel && d1.get(0).get_parallel_dim()==d2.get(0).get_parallel_dim() && OMPDParallelForLoop.IsSimilar(d2.get(0).get_pfor(), d1.get(0).get_pfor(), rd)) || both_serial){
					if(d1.get(0).IsEqual(d2.get(0), rd).equals(BOOLEAN.TRUE)){
						SectionSet set1 = new SectionSet();
						SectionSet set2 = new SectionSet();
						for(int j=1;j<d1.size();j++)
							set1.add(d1.get(j));
						for(int j=1;j<d2.size();j++)
							set2.add(d2.get(j));
						if(set1.IsEqual_xp(set2, rd))
							return true;
					}
				}
			}
		}
		return false;
	}
	
	private boolean containsSECTION_xp_old(SECTION e, RangeDomain rd){
		assert(e!=null);
	    if(e.isEmpty())
	    	return true;
		if(this.isEmpty())
			return false;
		for(int i=0;i<this.size();i++){
			boolean both_parallel = e.isParallel() && this.get(i).isParallel();
			boolean both_serial = e.isSerial() && this.get(i).isSerial();
			if((both_parallel && e.get_parallel_dim()==this.get(i).get_parallel_dim() && OMPDParallelForLoop.IsSimilar(this.get(i).get_pfor(), e.get_pfor(), rd)) || both_serial){
				if(e.isEqual(this.get(i), rd))
					return true;
			}
		}
		return false;
	}

public void Serialize(){
	for(SECTION e:this){
		e.Serialize();
	}
}

public void Expand(RangeDomain rd, Set<Symbol> Expand){
	SectionSet tmp = this.clone();
	this.clear();
	for(SECTION s:tmp){
		SectionSet e = s.Expand(rd, Expand);
		for(SECTION sec:e)
			this.add(sec,rd);
	}	
}

public void substituteKnowns(RangeDomain rd){
	SectionSet tmp = this.clone();
	this.clear();
	for(SECTION s:tmp){
		SectionSet e = s.substituteKnowns(rd);
		for(SECTION sec:e)
			this.add(sec,rd);
	}	
}
public void substituteKnowns_xp(RangeDomain rd){
	SectionSet tmp = this.clone();
	this.clear();
	for(SECTION s:tmp){
		SectionSet e = s.substituteKnowns(rd);
		for(SECTION sec:e)
			this.add_xp(sec,rd);
	}	
}
public void RemoveUnknwonSymbols(RangeDomain rd, Set<Symbol> Unknowns){
	SectionSet tmp = this.clone();
	this.clear();
	for(SECTION s:tmp){
		SECTION e = s.RemoveUnknwonSymbols(Unknowns);
		this.add(e,rd);
	}	
}

public void substitute(Symbol s, Expression expr, RangeDomain rd){
	SectionSet t = new SectionSet();
	for(SECTION e:this){
		t = t.unionWith(e.substitute(s, expr, rd), rd);
	}
	this.clear();
	for(SECTION e:t)
		this.add(e);
}
	
	
public interface SECTION extends Cloneable{
	public int get_dim_size();
	public int get_parallel_dim();
	public OMPDParallelForLoop get_pfor();
	public Expression get_parallel_coeff();
	
	public boolean isEmpty();
	public boolean isParallel();
	public boolean isSerial();
	public boolean isRSD();
	public boolean isERSD();
	public void Serialize();
	public SECTION clone();
	
    //public BOOLEAN IsSubsetOf(SECTION other, RangeDomain rd);
	//public BOOLEAN IsIndependent(SECTION other, RangeDomain rd);
	//public BOOLEAN IsEqual(SECTION other, RangeDomain rd);
	
	
	// these functions return true if BOOLEAN.TRUE, and return false if BOOLEAN.FALSE or BOOLEAN.UNKNOWN
	public boolean isIndependent(SECTION other, RangeDomain rd); 
	public boolean isEqual(SECTION other, RangeDomain rd);
	public boolean overlapsWith(SECTION other, RangeDomain rd);
	public boolean isSubsetOf(SECTION other, RangeDomain rd); 
	public boolean IsNeighbour(SECTION other, RangeDomain rd);
	public boolean containsInfiniteElement();
	public boolean containsSymbol(Symbol s);
	 
	public SectionSet Expand(RangeDomain rd, Set<Symbol> Expand);
	public SectionSet substituteKnowns(RangeDomain rd);
	public SectionSet substitute(Symbol s, Expression expr, RangeDomain rd);
	public SECTION RemoveUnknwonSymbols(Set<Symbol> Unknowns);
	public void ReplaceSymbol(Symbol s, Expression expr, RangeDomain rd);
	
	public SECTION intersectWith (SECTION other, RangeDomain rd);
	public SECTION unionWith (SECTION other, RangeDomain rd);
//	public SectionSet subtractFrom (SECTION other, RangeDomain rd);
	
}
	
public static class ERSD extends ArrayList<SectionSet.RSD> implements SECTION {

	private static final long serialVersionUID = 14L;

	// ERSD = rsd[0] - rsd[1] - rsd[2] - ... - rsd[n]
	
	public ERSD(){
		super();
	}
	
	public ERSD(RSD lhs, RSD rhs){
		super();
		add(lhs);
		add(rhs);
	}
	
	public ERSD(RSD lhs, SectionSet rhs_set){
		super();
		add(lhs);
		for(SECTION s: rhs_set){
			assert(s.isRSD());
			add((RSD)s);
		}
	}
	
	/**
     * Returns a clone object.
     */
    public ERSD clone(){
    	ERSD ersd = new ERSD();
        for(int i=0;i<this.size();i++){
        	ersd.add(this.get(i).clone());
        }
    	return ersd;
    }
    public String toString(){
    	String tmp="";
    	for(int i=0;i<this.size();i++){
    		tmp = tmp + this.get(i).toString();
    		if(i != this.size()-1)
    			tmp = tmp + " - ";
    	}
    	return tmp;
    }
	public int get_dim_size(){
		return this.get(0).get_dim_size();
	}
    public int get_parallel_dim(){
    	return this.get(0).get_parallel_dim();
    }
    public boolean isParallel(){
    	return this.get(0).isParallel();
    }
    public boolean isSerial(){
    	return this.get(0).isSerial();
    }
    public OMPDParallelForLoop get_pfor(){
    	return this.get(0).get_pfor();
    }
    public boolean isRSD(){
    	return false;
    }
	public boolean isERSD(){
		return true;
	}
	public void Serialize(){
		this.get(0).Serialize();
	}
	public SectionSet Expand(RangeDomain rd, Set<Symbol> Expand){
		ERSD tmp = new ERSD();
		for(int i=0;i<this.size();i++){
			RSD rsd = this.get(i).expand(rd, Expand);
			if(i==0)
				tmp.add(rsd);
			else if(!rsd.containsInfiniteElement())
				tmp.add(rsd);
		}
		if(tmp.IsEqual(this, rd).equals(BOOLEAN.TRUE))
			return new SectionSet (tmp);	
		return tmp.AddRSDtoRight(new RSD(), rd); // this is to simplify ERSD expression
	}
	public SectionSet substituteKnowns(RangeDomain rd){
		Set<Symbol> Expand=null;
		ERSD tmp = new ERSD();
		for(int i=0;i<this.size();i++){
			RSD rsd = this.get(i).substituteNonExpandables(rd,Expand);
			if(i==0)
				tmp.add(rsd);
			else if(!rsd.containsInfiniteElement())
				tmp.add(rsd);
		}
		if(tmp.IsEqual(this, rd).equals(BOOLEAN.TRUE))
			return new SectionSet (tmp);
		return tmp.AddRSDtoRight(new RSD(), rd); // this is to simplify ERSD expression
	}
	public SECTION RemoveUnknwonSymbols(Set<Symbol> Unknowns){
		ERSD tmp = new ERSD();
		for(int i=0;i<this.size();i++){
			RSD rsd = this.get(i).RemoveUnknwonSymbols(Unknowns);
			if(i==0)
				tmp.add(rsd);
			else if(!rsd.containsInfiniteElement())
				tmp.add(rsd);
		}
		if(tmp.size()==1)
			return tmp.get(0);
		else
		    return tmp;
	}
	public void ReplaceSymbol(Symbol s, Expression expr, RangeDomain rd){
		for(int i=0; i<this.size();i++)
			this.get(i).ReplaceSymbol(s, expr, rd);
	}
    public SectionSet substitute(Symbol s, Expression expr, RangeDomain rd){
    	ERSD ersd = (ERSD)clone();		
    	ersd.ReplaceSymbol(s, expr, rd);	
		  return ersd.AddRSDtoRight(new RSD(), rd);
	}
	public Expression get_parallel_coeff(){
		if(this.isSerial())
			return null;
		return this.get(0).get_parallel_coeff();
	}
	public boolean containsInfiniteElement(){
		for(int i=0;i<this.size();i++){
			if(this.get(i).containsInfiniteElement())
				return true;
		}
		return false;
	}
	public boolean containsRightTerm(RSD trm, RangeDomain rd){
		for(int j=1;j<size();j++)
			if(get(j).isEqual(trm, rd))
				return true;
		return false;
	}
	public boolean containsSymbol(Symbol s){
		for(int i=0;i<this.size();i++){
			if(this.get(i).containsSymbol(s))
				return true;
		}
		return false;
	}
    public BOOLEAN IsSubsetOf(SECTION other, RangeDomain rd){
		assert(other != null);
		if(this.isEmpty())
			return BOOLEAN.TRUE;
		if(other.isEmpty())
			return BOOLEAN.FALSE;
		if(other.isRSD())
			return this.get(0).IsSubsetOf((RSD)other, rd);
		else{
			ERSD o = (ERSD)other;
			if(this.get(0).isSubsetOf(o.get(0), rd)){
				boolean subset=true;
				for(int i=1;i<this.size();i++){
					subset = false;
					for(int j=1;j<o.size();j++)
						if(this.get(i).isSubsetOf(o.get(j), rd)){
							subset = true;
							break;
						}
					if(!subset)
						break;
				}
				if(subset)
					return BOOLEAN.TRUE;
			}
			if(this.IsEqual(o, rd).equals(BOOLEAN.TRUE))
				return BOOLEAN.TRUE;
			if(this.IsEqual(other, rd).equals(BOOLEAN.UNKNOWN))
				return BOOLEAN.UNKNOWN;
		}
		return BOOLEAN.FALSE;
	} 
    public boolean isSubsetOf(SECTION other, RangeDomain rd){
    	return this.IsSubsetOf(other, rd).equals(BOOLEAN.TRUE);
    }   
    public BOOLEAN IsEqual(SECTION other, RangeDomain rd){
    	if(other.isEmpty())
    		if(this.isEmpty())
    			return BOOLEAN.TRUE;
    		else
    			return  BOOLEAN.FALSE;
    	if(other.isRSD())
    		return BOOLEAN.FALSE;
    	if(this.size() != ((ERSD)other).size() )
			return BOOLEAN.FALSE;
    	BOOLEAN cond0 = this.get(0).IsEqual(((ERSD)other).get(0), rd);
    	if(cond0.equals(BOOLEAN.FALSE))
    		return BOOLEAN.FALSE;
    	else if(cond0.equals(BOOLEAN.UNKNOWN))
    		return BOOLEAN.UNKNOWN;
		for(int i=1;i<this.size();i++){
			BOOLEAN found = BOOLEAN.FALSE;
			for(int j=1;j<this.size();j++){
				BOOLEAN cond = this.get(i).IsEqual(((ERSD)other).get(j), rd);
				if(cond.equals(BOOLEAN.TRUE)){
					found=BOOLEAN.TRUE;
					break;
				}
				else if(cond.equals(BOOLEAN.UNKNOWN))
					found= BOOLEAN.UNKNOWN;
			}
			if(found!=BOOLEAN.TRUE)
				return found;
		}
		return BOOLEAN.TRUE;
    }
    
    public boolean isEqual(SECTION other, RangeDomain rd){
    	return this.IsEqual(other, rd).equals(BOOLEAN.TRUE);
    }
    
    public BOOLEAN IsIndependent(SECTION other, RangeDomain rd){
		if(other==null || other.isEmpty() || this.isEmpty())
			return BOOLEAN.TRUE;		
		if(other.isERSD()){
			BOOLEAN temp0 = this.get(0).IsIndependent(((ERSD)other).get(0), rd);
			if(temp0.equals(BOOLEAN.TRUE))
				return BOOLEAN.TRUE;
			RSD intrsct = ((ERSD)other).get(0).intersectWith(this.get(0), rd);
			if(intrsct==null) intrsct=((ERSD)other).get(0);
			for(int i=1;i<this.size();i++){
				BOOLEAN temp1=intrsct.IsSubsetOf(this.get(i), rd);
				if(temp1.equals(BOOLEAN.TRUE))
					return BOOLEAN.TRUE;
			}
			intrsct = ((ERSD)other).get(0).intersectWith(this.get(0), rd);
			if(intrsct==null) intrsct=this.get(0);
			for(int i=1;i<((ERSD)other).size();i++){
				BOOLEAN temp2=intrsct.IsSubsetOf(((ERSD)other).get(i), rd);
				if(temp2.equals(BOOLEAN.TRUE))
					return BOOLEAN.TRUE;
			}
			return temp0;
		}
		else{ // other is RSD
			BOOLEAN temp0=this.get(0).IsIndependent((RSD)other, rd);
			if(temp0.equals(BOOLEAN.TRUE))
				return BOOLEAN.TRUE;
			RSD intrsct = ((RSD)other).intersectWith(this.get(0), rd);
			if(intrsct==null) intrsct=(RSD)other;
			for(int i=1;i<this.size();i++){
				BOOLEAN temp2=intrsct.IsSubsetOf(this.get(i), rd);
				if(temp2.equals(BOOLEAN.TRUE))
					return BOOLEAN.TRUE;
			}
			return temp0;
		}
		
		
	}
    public boolean isIndependent(SECTION other,RangeDomain rd){
    	return this.IsIndependent(other, rd).equals(BOOLEAN.TRUE);
    }
    public boolean overlapsWith(SECTION other,RangeDomain rd){
    	return this.IsIndependent(other, rd).equals(BOOLEAN.FALSE);
    }

    /** ersd isNeighbour to rsd if   */
    public boolean IsNeighbour(SECTION other, RangeDomain rd){
    	if(other.isRSD()){ // and ersd and rsd sections are neigbours only of rsd and ersd_left_term are neighbours
    		if( this.get(0).isIndependent((SectionSet.RSD)other, rd) && this.get(0).IsNeighbour((SectionSet.RSD)other, rd)){
    			for(int j=1;j<this.size();j++)
    				if(!other.isIndependent(this.get(j), rd))
    					return false;
    			return true;
    		}
    	}
    	else{
    		if(this.get(0).isIndependent(((SectionSet.ERSD)other).get(0), rd) && this.get(0).IsNeighbour(((SectionSet.ERSD)other).get(0), rd)){
    			for(int j=1;j<((SectionSet.ERSD)other).size();j++)
    				if(!((SectionSet.ERSD)other).get(j).isIndependent(this.get(0), rd))
    					return false;
    			for(int j=1;j<this.size();j++)
    				if(!((SectionSet.ERSD)other).get(0).isIndependent(this.get(j), rd))
    					return false;
    			return true;
    		}
    	}
    	return false;
    }     
    public SECTION intersectWith (SECTION other, RangeDomain rd){
    	if(other == null)
    		return new RSD();
    	if(this.isEmpty() || other.isEmpty())
    		return new RSD();
    	assert(this.get_dim_size() == other.get_dim_size());
    	if(this.IsIndependent(other, rd).equals(BOOLEAN.TRUE))
    		return new RSD();
    	if(this.isSubsetOf(other, rd))
    		return this.clone();
    	if(other.isSubsetOf(this, rd))
    		return other.clone();
    	return null;
    }
   
    public SECTION unionWith (SECTION other, RangeDomain rd){
    	if(other==null || other.isEmpty())
    		return this.clone();
    	if(this.isEmpty())
    		return other.clone();
    	assert(this.get_dim_size() == other.get_dim_size());
    	if(this.IsSubsetOf(other, rd).equals(BOOLEAN.TRUE))
    		return other.clone();
    	return null;
    }
    
    public SectionSet AddRSDtoRight (RSD other, RangeDomain rd){
    	if(this.get(0).IsSubsetOf(other, rd).equals(BOOLEAN.TRUE)){
    		return new SectionSet();
    	}
    	SectionSet right_terms;
    	if(other.isEmpty())
    		right_terms = new SectionSet();
    	else
    		right_terms = new SectionSet(other.clone());
    	for(int i=1;i<this.size();i++)
    		right_terms.add(this.get(i), rd);
    	return SectionSet.subtractSetFromSection(this.get(0), right_terms, rd);  	

    }
		
} // end of SectionSet.ERSD

public static class RSD extends ArrayList<SectionSet.ELEMENT> implements SECTION {
	
	private static final long serialVersionUID = 13L;

	//this constructor is used to instantiate RSD sections inside a parallel region
	public RSD (ArrayAccess ar, RangeDomain rd, Set<Symbol> Expand, OMPDParallelForLoop pfor){
		super();
		Symbol parallel_index = pfor.get_parallel_loop_index();
		for(int i=0;i<ar.getNumIndices();i++){
			ELEMENT elem = new ELEMENT(ar.getIndex(i), rd);
			elem.set_pfor(pfor);
			elem.Expand(rd, Expand);
			if(DataFlowTools.getUseSymbol(ar.getIndex(i)).contains(parallel_index)){
				elem.MakeParallel();
				if(!OMPDTools.isNonLinear(ar.getIndex(i),parallel_index)){
					Expression coeff = OMPDTools.getCoefficient(ar.getIndex(i), parallel_index);
					assert (coeff!= null);
					elem.set_access_coeff(coeff);
				}
			}
			else{
				Expression coeff=null;
				for(Symbol s: DataFlowTools.getUseSymbol(ar.getIndex(i))){
					Expression rng = rd.getRange(s);
					if(rng!=null && !(rng instanceof RangeExpression) && DataFlowTools.getUseSymbol(rng).contains(parallel_index)){
						if(!OMPDTools.isNonLinear(ar.getIndex(i),s) && !OMPDTools.isNonLinear(rng,parallel_index)){
							Expression coeff1 = OMPDTools.getCoefficient(ar.getIndex(i), s);
							Expression coeff2 = OMPDTools.getCoefficient(rng, parallel_index);
							assert (coeff1!= null);
							assert (coeff2!= null);
							if(coeff==null)
								coeff = new IntegerLiteral(0);
							coeff = Symbolic.add(coeff, Symbolic.multiply(coeff1,coeff2));
						}
					}	
				}
				if(coeff!=null){
					elem.MakeParallel();
					elem.set_access_coeff(coeff);
				}
			}
			/*else 
				elem.MakeSerial();*/ //default is already serial
			this.add(elem);
			//now i am going to add relevant variables to allow a RSD to be a RangeSection
		}
	}
	
	//this constructor is used to instantiate RSD sections inside a serial region
	public RSD (ArrayAccess ar, RangeDomain rd, Set<Symbol> Expand){
		super();
		for(int i=0;i<ar.getNumIndices();i++){
			ELEMENT elem = new ELEMENT(ar.getIndex(i), rd);
			elem.Expand(rd, Expand);
			//elem.MakeSerial(); //default is already serial
			this.add(elem); 
		}
	}
	
	public RSD(){
		super();
	}
	
	/**
     * Returns a clone object.
     */
    public RSD clone(){
    	RSD rsd = new RSD();
        for(int i=0;i<this.size();i++){
        	rsd.add(this.get(i).clone());
        }
    	return rsd;
    }
    public String toString(){
    	String tmp="";
    	for(int i=0;i<this.size();i++){
    		tmp = tmp + this.get(i).toString();    		
    	}
    	return tmp;
    }
	public int get_dim_size(){
    	return this.size();
    }
    public int get_parallel_dim(){
    	if(this.isEmpty())
    		return -1;
    	for(int i=0;i<this.size();i++)
    		if(this.get(i).isParallel())
    			return i;
    	return -1;
    	
    }
    public boolean isParallel(){
    	return this.get_parallel_dim() != -1;
    }
    public boolean isSerial(){
    	return this.get_parallel_dim() == -1;
    }
    public OMPDParallelForLoop get_pfor(){
    	for(int i=0;i<this.size();i++)
    		if(this.get(i).get_pfor() != null)
    			return this.get(i).get_pfor();
    	return null;
    }
    public boolean isRSD(){
    	return true;
    }
	public boolean isERSD(){
		return false;
	}
	public void Serialize(){
		for(int i=0;i<this.get_dim_size();i++){
			if(this.get(i).isParallel())
				this.get(i).MakeSerial();
		}
	}
	public boolean containsInfiniteElement(){
		for(int i=0;i<this.size();i++){
			if(this.get(i).containsInfiniteElement())
				return true;
		}
		return false;
	}
	public boolean containsSymbol(Symbol s){
		for(int i=0;i<this.size();i++){
			if(this.get(i).containsSymbol(s))
				return true;
		}
		return false;
	}
	public boolean IsInfiniteRSD(){
		for(int i=0;i<this.size();i++){
			if(!this.get(i).IsInfiniteElement())
				return false;
		}
		return true;
	}
	public void replaceInfiniteElements(){
		for(int i=0;i<this.size();i++){
			if(this.get(i).containsInfiniteElement()){
				this.get(i).replaceInfiniteElements();
				if(i == this.get_parallel_dim())
					this.get(i).MakeSerial();
			}
		}
	}
	public SectionSet Expand(RangeDomain rd, Set<Symbol> Expand){
		return new SectionSet(this.expand(rd, Expand));
	}
	private RSD expand(RangeDomain rd, Set<Symbol> Expand){
		RSD tmp = new RSD();
		for(int i=0; i<this.get_dim_size();i++){
			tmp.add(this.get(i).Expand(rd, Expand));
		}
		return tmp;
	}
	public SectionSet substituteKnowns(RangeDomain rd){
		Set<Symbol> Expand=null;
		RSD tmp = clone().substituteNonExpandables(rd, Expand);
		return new SectionSet(tmp);
	}
	private RSD substituteNonExpandables(RangeDomain rd, Set<Symbol> Expand){
		RSD tmp = clone();
		for(int i=0; i<tmp.get_dim_size();i++)
			tmp.get(i).substituteNonExpandables(rd, Expand);
		return tmp;
	}
	
	public RSD RemoveUnknwonSymbols(Set<Symbol> Unknowns){
		RSD tmp = new RSD();
		for(int i=0; i<this.get_dim_size();i++){
			tmp.add(this.get(i).RemoveUnknwonSymbols(Unknowns));
		}
		return tmp;
	}
	public void ReplaceSymbol(Symbol s, Expression expr, RangeDomain rd){
		for(int i=0; i<this.get_dim_size();i++)
			this.get(i).substitute(s, expr, rd);
	}
	public SectionSet substitute(Symbol s, Expression expr, RangeDomain rd){
		RSD rsd = clone();

		
		rsd.ReplaceSymbol(s, expr, rd);
		  return new SectionSet(rsd);
	}
	public Expression get_parallel_coeff(){
		if(this.isSerial())
			return null;
		return this.get(this.get_parallel_dim()).get_access_coeff();
	}
	public void set_FullSized(ArraySpecifier acc){
		for(int i=0;i<this.get_dim_size();i++){
			this.get(i).set_full_size_element(new IntegerLiteral(0) , Symbolic.subtract(acc.getDimension(i), new IntegerLiteral(1)),new IntegerLiteral(1));
		}
	}
	/** swap the element of dimension i with the new passed element */
	public RSD replaceELEMENT(int dimension_num, ELEMENT elm){
		RSD t = this.clone();
		elm.set_full_size_element(t.get(dimension_num).full_size.clone());
		t.remove(dimension_num);
		t.add(dimension_num, elm);
		return t;
	}
	public BOOLEAN IsIndependent(SECTION other, RangeDomain rd){
		if(other==null || other.isEmpty() || this.isEmpty())
			return BOOLEAN.TRUE;
		assert(this.get_dim_size() == other.get_dim_size());
		if(other.isRSD())
			return this.IsIndependent((RSD)other, rd);
		else
			return ((ERSD)other).IsIndependent(this, rd);
	}
	public boolean isIndependent(SECTION other,RangeDomain rd){
    	return this.IsIndependent(other, rd).equals(BOOLEAN.TRUE);
    }
	private BOOLEAN IsIndependent(RSD other, RangeDomain rd){
		BOOLEAN res = BOOLEAN.FALSE;
		for(int i=0;i<this.get_dim_size();i++){
			BOOLEAN b = ELEMENT.IsIndependent(this.get(i), other.get(i), rd);
			if(b.equals(BOOLEAN.TRUE))
				return BOOLEAN.TRUE;
			else if(b.equals(BOOLEAN.UNKNOWN))
				res= BOOLEAN.UNKNOWN;
		}
		return res;
	}
	public boolean overlapsWith(SECTION other,RangeDomain rd){
    	return this.IsIndependent(other, rd).equals(BOOLEAN.FALSE);
    }
    
    public BOOLEAN IsSubsetOf(SECTION other, RangeDomain rd){
		assert(other != null);
		if(this.isEmpty())
			return BOOLEAN.TRUE;
		if(other.isEmpty())
			return BOOLEAN.FALSE;
		assert(this.get_dim_size() == other.get_dim_size());
		if(other.isRSD()){
			for(int i=0;i<this.get_dim_size();i++){
				BOOLEAN within = ELEMENT.IsSubsetOf(this.get(i), ((RSD)other).get(i), rd);	
				if(within == BOOLEAN.FALSE)
					return BOOLEAN.FALSE;
				else if(within.equals(BOOLEAN.UNKNOWN))
					return BOOLEAN.UNKNOWN;
			}
			return BOOLEAN.TRUE;
		}
		else{
			ERSD o = (ERSD)other;
			for(int j=1;j<o.size();j++)
				if(!this.isIndependent(o.get(j), rd))
					return BOOLEAN.FALSE;
			return this.IsSubsetOf(o.get(0), rd);	
		}
	}

	
	public boolean isSubsetOf(SECTION other, RangeDomain rd){
    	return this.IsSubsetOf(other, rd).equals(BOOLEAN.TRUE);
    }
	
	public BOOLEAN IsEqual(SECTION other, RangeDomain rd){
		if(other == null)
			return BOOLEAN.FALSE;
		if(other.isEmpty())
			if(this.isEmpty())
				return BOOLEAN.TRUE;
			else
				return BOOLEAN.FALSE;
		assert(this.get_dim_size() == other.get_dim_size());
		if(other.isERSD())
    		return BOOLEAN.FALSE;
		return this.IsEqual((RSD)other, rd);

	}
	
	private BOOLEAN IsEqual(RSD other, RangeDomain rd){
		for(int i=0;i<this.get_dim_size();i++){
			BOOLEAN eq = ELEMENT.IsEqual(this.get(i), other.get(i), rd);	
			if(eq == BOOLEAN.FALSE)
				return BOOLEAN.FALSE;
			else if(eq.equals(BOOLEAN.UNKNOWN))
				return BOOLEAN.UNKNOWN;
		} 
		return BOOLEAN.TRUE;
	}
	
	public boolean isEqual(SECTION other, RangeDomain rd){
    	return this.IsEqual(other, rd).equals(BOOLEAN.TRUE);
    }

	public boolean IsNeighbour(SECTION other, RangeDomain rd){
		if(other.isRSD())
			return this.IsNeighbour((SectionSet.RSD)other, rd);
		else
			return ((SectionSet.ERSD)other).IsNeighbour(this, rd);
	}
/** rsd_a isNeighbour to rsd_b if all of their elements are equal except for one element which is neighbour  */
	private boolean IsNeighbour(RSD other, RangeDomain rd){
		//assert(this.IsIndependent(other, rd));
		int num_of_indpenedent_dims = 0;
		int independent_dim=-1;
		for(int i=0;i<this.get_dim_size();i++){
			BOOLEAN indep = ELEMENT.IsIndependent(this.get(i), other.get(i), rd);
			if(indep.equals(BOOLEAN.TRUE)){
				num_of_indpenedent_dims++;
				independent_dim = i;
			}
			else{
				if(ELEMENT.IsEqual(this.get(i), other.get(i), rd).equals(BOOLEAN.FALSE))
					return false;
			}
		}
		if(num_of_indpenedent_dims==1)
			if(ELEMENT.IsNeighbour(this.get(independent_dim), other.get(independent_dim), rd))
				return true;
		return false;
	}
	
    
    public SECTION intersectWith (SECTION other, RangeDomain rd){
    	if(other == null)
    		return new RSD();
    	if(this.isEmpty() || other.isEmpty())
    		return new RSD();
    	assert(this.get_dim_size() == other.get_dim_size());
    	if(other.isERSD())
    		return ((ERSD)other).intersectWith(this, rd);
    	else
    		return this.intersectWith((RSD)other, rd);
    }
    
    private RSD intersectWith (RSD other, RangeDomain rd){
    	RSD tmp = new RSD();
    	for(int i=0;i<this.get_dim_size();i++){
    		ELEMENT elm = ELEMENT.intersect(this.get(i), other.get(i), rd);
    		if(elm==null)
    			return null;
    		if(elm.isEmpty())
    			return new RSD();
    		tmp.add(elm);
    	}
    	return tmp;
    }
    
    public SECTION unionWith (SECTION other, RangeDomain rd){
    	if(other==null || other.isEmpty())
    		return this.clone();
    	if(this.isEmpty())
    		return other.clone();
    	assert(this.get_dim_size() == other.get_dim_size());
    	if(other.isERSD())
    		return ((ERSD)other).unionWith(this, rd);
    	else 
    		return this.unionWith((RSD)other, rd);
    }
    
    private RSD unionWith (RSD other, RangeDomain rd){
    	RSD tmp = new RSD();
    	for(int i=0;i<this.get_dim_size();i++){
    		ELEMENT elm = ELEMENT.union(this.get(i), other.get(i), rd);
    		if(elm==null)
    			return null;
    		tmp.add(elm);
    	}
    	return tmp;
    }
 /*   
    public SectionSet subtractFrom (SECTION other, RangeDomain rd){
    	if(this.isEmpty())
    		return new SectionSet();
    	if(other==null || other.isEmpty())
    		return new SectionSet(this.clone());
    	if(other.isERSD())
    		return ((ERSD)other).subtractFrom(this, rd);
    	else
    		return this.subtractFrom((RSD)other, rd);
    }
 */   
    
    public SectionSet subtractFrom (RSD other, RangeDomain rd){
    	if(this.isEmpty())
    		return new SectionSet();
    	if(other==null || other.isEmpty())
    		return new SectionSet(this.clone());
    	if(this.IsInfiniteRSD())
    		return null;
    	RSD intrsct = this.intersectWith(other, rd);
    	if(intrsct==null){
    		/*SectionSet set = new SectionSet();
    		set.add(new ERSD(this.clone(), other.clone()));
    		return set;*/
    		return null;
    	}
    	
    	if(intrsct.isEmpty()){
    		SectionSet set = new SectionSet();
    		set.add(this.clone());
    		return set;
    	}
    	if(this.IsEqual(intrsct, rd).equals(BOOLEAN.TRUE))
    		return new SectionSet();   	
    	
    	LinkedHashMap<Integer,ArrayList<ELEMENT>> map = new LinkedHashMap<Integer,ArrayList<ELEMENT>>();
    	for(int i=0;i<this.get_dim_size();i++){
    		ArrayList<ELEMENT> tmp = ELEMENT.subtract(this.get(i), intrsct.get(i), rd);
    		if(tmp==null)
    			return null;
    		map.put(i, tmp);	
    	}
    	SectionSet set = new SectionSet();
    	for(int i=0;i<this.get_dim_size();i++){
    		for(int j=0;j<map.get(i).size();j++){
    			ELEMENT tmp = map.get(i).get(j);
    			RSD rsd = new RSD();
    			for(int k=0;k<i;k++)
    				rsd.add(k,intrsct.get(k).clone());
    			rsd.add(i,tmp);
    			for(int k=i+1;k<this.get_dim_size();k++)
    				rsd.add(k,this.get(k).clone());
    			set.add(rsd);
    		}
    	}
    	
    	return set;
    }
    
	
} // end of SectionSet.RSD

public static class ELEMENT extends ArrayList<Expression> implements Cloneable{
	// [ ELEMENT[0]:ELEMENT[1]:ELEMENT[2] ] = [lower:upper:stride]
	private static final long serialVersionUID = 11L;
	private SECTION_ACCESS access;
	private OMPDParallelForLoop pfor;
	private Expression access_coeff;
	private ELEMENT full_size;
	private DIRECTION direction;
	
	public ELEMENT()
    {
      super();
      pfor=null;
      access = SECTION_ACCESS.serial;
    }
	
	public ELEMENT(Expression LB, Expression UB, Expression STRD)
    {
      super();
      this.add(0,LB);
      this.add(1,UB);
      this.add(2,STRD);
      determine_direction(null);
      pfor=null;
      access_coeff=null;
      access = SECTION_ACCESS.serial;
    }
	
	public ELEMENT (Expression ar){
		super();
	      this.add(0,ar.clone());
	      this.add(1,ar.clone());
	      this.add(2,computeSTRIDE(ar.getStatement(), ar));
	      determine_direction(null);
	      pfor=null;
	      access_coeff=null;
	      access = SECTION_ACCESS.serial;
	}
	
	public ELEMENT (Expression ar, RangeDomain rd){
		super();
		Expression tmp = ar.clone();
		if(rd!=null){
			for(Symbol s:DataFlowTools.getUseSymbol(ar)){
				Expression exp = rd.getRange(s);
				if(exp!=null && !(exp instanceof RangeExpression)){
					tmp = rd.substituteForward(tmp, s);
				}
			}
		}
		
	      this.add(0,tmp.clone());
	      this.add(1,tmp.clone());
	      this.add(2,computeSTRIDE(ar.getStatement(), tmp));
	      determine_direction(rd);
	      pfor=null;
	      access_coeff=null;
	      access = SECTION_ACCESS.serial;
	}
	
	/**
     * Returns a clone object.
     */
    public ELEMENT clone(){
    	if(this.isEmpty())
    		return new ELEMENT();
    	ELEMENT elem = new ELEMENT(this.getLB().clone(),this.getUB().clone(),this.getSTRIDE().clone());
    	if(this.isParallel())
    		elem.MakeParallel();
    	if(this.get_pfor()!=null)
    		elem.set_pfor(this.get_pfor());
    	elem.set_full_size_element(this.full_size);
    	if(this.access_coeff!=null)
    		elem.access_coeff = this.access_coeff.clone();
    	elem.direction = this.direction;
    	return elem;
    }
    public String toString(){
    	if(this.isEmpty()) return "[]";
    	String temp = this.getLB().toString()+":"+this.getUB().toString()+":"+this.getSTRIDE().toString();
    	/*if(this.isRangeElement()){
    		temp = temp.replaceAll(this.varyingSymbol.toString(), this.varyingSymbol.toString()+"'");
    	}*/
    	if(this.isParallel())
			temp= "[Pr("+temp+"]";
		else
			temp= "["+temp+"]";  
    	return temp;
    }
	public void MakeSerial(){
		this.access = SECTION_ACCESS.serial;
		//this.pfor = null;
		this.access_coeff=null;
	}
	public void MakeParallel(){
		this.access = SECTION_ACCESS.parallel;
	}
    public boolean isParallel(){
	    return this.access == SECTION_ACCESS.parallel;
	}
	public boolean isSerial(){
		return this.access == SECTION_ACCESS.serial;
	}
	public boolean isEmpty(){
	    return this.size()==0;
	}
	public void set_access_coeff(Expression exp){
		this.access_coeff = exp;
	}
	public Expression get_access_coeff(){
		return this.access_coeff;
	}
	public OMPDParallelForLoop get_pfor(){
		return this.pfor;
	}
	public void set_pfor(OMPDParallelForLoop lp){
		this.pfor = lp;
	}
	public Expression getLB(){
		if(this.isEmpty())
			return null;
		else
			return this.get(0);
	}
	public Expression getUB(){
		if(this.isEmpty())
			return null;
		else
			return this.get(1);
	}
	public Expression getSTRIDE(){
		if(this.isEmpty())
			return null;
		else
			return this.get(2);
	}
	private boolean IsUnitStride(){
		return this.getSTRIDE().equals(new IntegerLiteral(1)) || this.getSTRIDE().equals(new IntegerLiteral(-1));
	}
	private boolean IsTwoStride(){
		return this.getSTRIDE().equals(new IntegerLiteral(2)) || this.getSTRIDE().equals(new IntegerLiteral(-2));
	}
	private void determine_direction(RangeDomain rd1){ //return true if stride is positive
		int sign = OMPDTools.expression_sign(this.getSTRIDE(), rd1);
		if(sign==0)
			Tools.exit("ERROR in determine_direction() in SectionSet: Unknwon Stride direction");
		if(sign==-1)
			direction= DIRECTION.BACKWARD;
		else // sign=1
			direction= DIRECTION.FORWARD;
	}
	public boolean IsForward(){ //return true if stride is positive
		if(direction==DIRECTION.BACKWARD)
			return false;
		else
			return true;
	}
	public boolean IsBackward(){ //return true if stride is negative
		if(direction==DIRECTION.BACKWARD)
			return true;
		else
			return false;
	}
	public boolean IsInfiniteElement(){
		return (this.getLB().equals(new InfExpression(-1) )) &&
			   (this.getUB().equals(new InfExpression(1)));
	}
	public boolean containsInfiniteElement(){
		return (this.getLB().equals(new InfExpression(-1) )) ||
			   (this.getUB().equals(new InfExpression(1)));
	}
	public void replaceInfiniteElements(){
		if(this.getLB().equals(new InfExpression(-1) )){
			this.remove(0);
			this.add(0,full_size.get(0).clone());
		}
		if(this.getUB().equals(new InfExpression(1))){
			this.remove(1);
			this.add(1,full_size.get(1).clone());
		}
	}
	public void set_full_size_element(Expression lb, Expression ub, Expression str){
    	this.full_size = new ELEMENT(lb,ub,str );
    }
	public void set_full_size_element(ELEMENT elm){
		this.full_size = elm;
	}
	public boolean isFullSized(){
		return this.getLB().equals(this.full_size.getLB()) &&
				this.getUB().equals(this.full_size.getUB()) &&
				this.getSTRIDE().equals(this.full_size.getSTRIDE());
	}
	public boolean containsSymbol(Symbol s){
		if(SymbolTools.getAccessedSymbols(this.getLB()).contains(s))
			return true;
		if(SymbolTools.getAccessedSymbols(this.getUB()).contains(s))
			return true;
		if(SymbolTools.getAccessedSymbols(this.getSTRIDE()).contains(s))
			return true;
		return false;
	}
	private Expression computeSTRIDE(Statement stmt , Expression ar ){
//		Statement stmt = ar.getStatement();
		ForLoop forloop=IRTools.getAncestorOfType(stmt, ForLoop.class);
		Set<Symbol> smbls =DataFlowTools.getUseSymbol(ar);
		if(smbls.isEmpty())
			return new IntegerLiteral(1); //no index -- only one element is accessed
		Symbol index=null;
		
		while(forloop!=null){
			if(smbls.contains(LoopTools.getLoopIndexSymbol(forloop))){
				index=LoopTools.getLoopIndexSymbol(forloop);
				break;
			}
			forloop=IRTools.getAncestorOfType(forloop, ForLoop.class);
		}
		
		if(ar==null || index == null){
			return new IntegerLiteral(1); 
		}
		
		// I need to test if linear expression
		if(OMPDTools.isNonLinear(ar,index))
			return new IntegerLiteral(1); 
		
		return Symbolic.multiply(OMPDTools.getCoefficient(ar, index), LoopTools.getIncrementExpression(forloop).clone());
		

		//	return Symbolic.simplify(new BinaryExpression (OMPDTools.findCoefficient(ar, index),BinaryOperator.MULTIPLY,LoopTools.getIncrementExpression(forloop).clone()));

	}

	public ELEMENT Expand(RangeDomain rd1, Set<Symbol> Expand){
		ELEMENT tmp = this.clone();
		RangeDomain rd;
		if(rd1==null)
			rd=new RangeDomain();
		else
			rd=rd1;
		if(Expand==null || Expand.isEmpty()){
			tmp.substituteNonExpandables(rd,Expand);
			return tmp;
		}
		Expression lower=null, upper=null, stride=null;
		
		for(Symbol e : DataFlowTools.getUseSymbol(this.getSTRIDE()))
			if(Expand.contains(e)){
				if(OMPDTools.isNonLinear(this.getSTRIDE(), e)){
					stride = new IntegerLiteral(1);
					break;
				}
				else{
					Expression rng = rd.getRange(e);
					if(rng instanceof RangeExpression)
						stride = Symbolic.simplify(IRTools.replaceSymbol(this.getSTRIDE(), e, ((RangeExpression) rng).getUB()));
				}
			}
		if(stride!=null){
			tmp.remove(2);
			tmp.add(2, stride);
			determine_direction(rd);
		}
		
		for(Symbol e : DataFlowTools.getUseSymbol(this.getLB())){
			if(Expand.contains(e)){
				if(OMPDTools.isNonLinear(this.getLB(), e)){
					if(IsForward())
						lower = new InfExpression(-1);
					else //direction=-1
						lower = new InfExpression(1);
					break;
				}
				else{
					Expression rng = rd.getRange(e);
					if(rng instanceof RangeExpression){
						if(IsForward())
							lower = Symbolic.simplify(IRTools.replaceSymbol(this.getLB(), e, ((RangeExpression) rng).getLB())); // lower expression
						else //direction=-1
							lower = Symbolic.simplify(IRTools.replaceSymbol(this.getLB(), e, ((RangeExpression) rng).getUB())); // lower expression
					}
				}
			}
		}
		if(lower!=null){
			tmp.remove(0);
			tmp.add(0, lower);
		}

		for(Symbol e : DataFlowTools.getUseSymbol(this.getUB()))
			if(Expand.contains(e)){
				if(OMPDTools.isNonLinear(this.getUB(), e)){
					if(IsForward())
						upper = new InfExpression(1);
					else //direction=-1
						upper = new InfExpression(-1);
					break;
				}
				else{
					Expression rng = rd.getRange(e);
					if(rng instanceof RangeExpression){
						if(IsForward())
							upper = Symbolic.simplify(IRTools.replaceSymbol(this.getUB(), e, ((RangeExpression) rng).getUB())); // upper expression
						else //direction=-1
							upper = Symbolic.simplify(IRTools.replaceSymbol(this.getUB(), e, ((RangeExpression) rng).getLB())); // upper expression
					}
				}
			}
		if(upper!=null){
			tmp.remove(1);
			tmp.add(1, upper);
		}

		
		tmp.substituteNonExpandables(rd,Expand);
		return tmp;
	}
	
	public void substituteNonExpandables(RangeDomain rd, Set<Symbol> Expand){
		boolean found_parallel_symbol_in_lb=false, found_parallel_symbol_in_ub=false;
		for(Symbol e : DataFlowTools.getUseSymbol(this.getSTRIDE())){
			if(Expand != null && Expand.contains(e))
				continue;
			Expression value = rd.getRange(e);
			if(value != null && !(value instanceof RangeExpression)){
				Expression tmp = rd.substituteForward(this.getSTRIDE(),e);
				this.remove(2);
				this.add(2,tmp);
				determine_direction(rd);
			}
		}
		for(Symbol e : DataFlowTools.getUseSymbol(this.getUB())){
			if(Expand != null && Expand.contains(e))
				continue;
			Expression value = rd.getRange(e);
			if(value != null && !(value instanceof RangeExpression)){
				Expression tmp = rd.substituteForward(this.getUB(),e);
				if(this.get_pfor()!=null)
					if(SymbolTools.getAccessedSymbols(tmp).contains(this.get_pfor().get_parallel_loop_index()))
						found_parallel_symbol_in_lb = true;
				this.remove(1);
				this.add(1,tmp);
			}
		}
		for(Symbol e : DataFlowTools.getUseSymbol(this.getLB())){
			if(Expand != null && Expand.contains(e))
				continue;
			Expression value = rd.getRange(e);
			if(value != null && !(value instanceof RangeExpression)){
				Expression tmp = rd.substituteForward(this.getLB(),e);
				if(this.get_pfor()!=null)
					if(SymbolTools.getAccessedSymbols(tmp).contains(this.get_pfor().get_parallel_loop_index()))
						found_parallel_symbol_in_ub = true;
				this.remove(0);
				this.add(0,tmp);
			}
		}
		if(found_parallel_symbol_in_lb && found_parallel_symbol_in_ub)
			if(rd.isEQ(this.getLB(),this.getUB())){
				this.MakeParallel();
				if(!OMPDTools.isNonLinear(this.getLB(),this.get_pfor().get_parallel_loop_index())){
					Expression coeff = OMPDTools.getCoefficient(this.getLB(), this.get_pfor().get_parallel_loop_index());
					assert (coeff!= null);
					this.set_access_coeff(coeff);
				}
			}
	}
	
	public void substitute(Symbol s, Expression expr, RangeDomain rd){
		for(Symbol e : DataFlowTools.getUseSymbol(this.getSTRIDE())){
			if(e.equals(s)){
				Expression tmp = Symbolic.simplify(IRTools.replaceSymbol(this.get(2), s, expr));
				if(rd!=null) tmp = rd.substituteForward(tmp);
				this.remove(2);
				this.add(2,tmp);
				break;
			}
		}
		for(Symbol e : DataFlowTools.getUseSymbol(this.getUB())){
			if(e.equals(s)){
				Expression tmp = Symbolic.simplify(IRTools.replaceSymbol(this.get(1), s, expr));
				if(rd!=null) tmp = rd.substituteForward(tmp);
				this.remove(1);
				this.add(1,tmp);
				break;
			}
		}
		for(Symbol e : DataFlowTools.getUseSymbol(this.getLB())){
			if(e.equals(s)){
				Expression tmp = Symbolic.simplify(IRTools.replaceSymbol(this.get(0), s, expr));
				if(rd!=null) tmp = rd.substituteForward(tmp);
				this.remove(0);
				this.add(0,tmp);
				break;
			}
		}
	}
	
	public void substituteSymbolwithRange(Symbol index, Expression lb, Expression ub, Expression stride, RangeDomain rd){
		Expression l=null,u=null;
		if(IsForward()){
			switch(OMPDTools.expression_sign(stride, rd)){
				case 0:
					Tools.exit("ERROR in SectionSet.java: Unknwon Stride expression");
					break;
				case 1:
					 l = Symbolic.simplify(IRTools.replaceSymbol(this.get(0), index, lb));
					if(rd!=null) l = rd.substituteForward(l);
					 u = Symbolic.simplify(IRTools.replaceSymbol(this.get(1), index, ub));
					if(rd!=null) u = rd.substituteForward(u);
					break; 
				case -1:
					 l = Symbolic.simplify(IRTools.replaceSymbol(this.get(0), index, ub));
					if(rd!=null) l = rd.substituteForward(l);
					 u = Symbolic.simplify(IRTools.replaceSymbol(this.get(1), index, lb));
					if(rd!=null) u = rd.substituteForward(u);
			}
		}
		else{
			switch(OMPDTools.expression_sign(stride, rd)){
			case 0:
				Tools.exit("ERROR in SectionSet.java: Unknwon Stride expression");
				break;
			case 1:
				 l = Symbolic.simplify(IRTools.replaceSymbol(this.get(0), index, ub));
				if(rd!=null) l = rd.substituteForward(l);
				 u = Symbolic.simplify(IRTools.replaceSymbol(this.get(1), index, lb));
				if(rd!=null) u = rd.substituteForward(u);
				break; 
			case -1:
				 l = Symbolic.simplify(IRTools.replaceSymbol(this.get(0), index, lb));
				if(rd!=null) l = rd.substituteForward(l);
				 u = Symbolic.simplify(IRTools.replaceSymbol(this.get(1), index, ub));
				if(rd!=null) u = rd.substituteForward(u);
		    }
		}
		this.remove(0);
		this.add(0, l);
		this.remove(1);
		this.add(1, u);
	}
	
	public ELEMENT RemoveUnknwonSymbols(Set<Symbol> Unknowns){
		ELEMENT tmp = this.clone();
		if(Unknowns==null || Unknowns.isEmpty())
			return tmp;
		
		for(Symbol e : DataFlowTools.getUseSymbol(this.getSTRIDE()))
			if(Unknowns.contains(e)){
				tmp.remove(2);
				if(this.IsForward())
					tmp.add(2, new IntegerLiteral(1));
				else
					tmp.add(2, new IntegerLiteral(-1));
				break;
			}

		for(Symbol e : DataFlowTools.getUseSymbol(this.getLB())){
			if(Unknowns.contains(e)){
				tmp.remove(0);
				if(IsForward())
					tmp.add(0, new InfExpression(-1) );
				else
					tmp.add(0, new InfExpression(1) );
				break;
			}
		}

		for(Symbol e : DataFlowTools.getUseSymbol(this.getUB()))
			if(Unknowns.contains(e)){
				tmp.remove(1);
				if(IsForward())
					tmp.add(1, new InfExpression(1));
				else
					tmp.add(1, new InfExpression(-1));
				break;
			}

		return tmp;
		
	}
	
    public static RELATION relationship (ELEMENT elm1, ELEMENT elm2, RangeDomain rd){
		
		if(elm1.IsInfiniteElement() && elm2.IsInfiniteElement())
			return RELATION.EQUAL;
		
		if(elm1.isFullSized() && elm2.isFullSized())
			return RELATION.EQUAL;
		
		if(elm2.IsInfiniteElement() || elm2.isFullSized())
			return RELATION.SUBSETOF;
		
		if(elm1.IsInfiniteElement() || elm1.isFullSized())
			return RELATION.SUBSUMES;
		
		if(elm1.getLB().equals(elm2.getLB()) && elm1.getUB().equals(elm2.getUB()) && elm1.getSTRIDE().equals(elm2.getSTRIDE()))
			return RELATION.EQUAL;
		
		return range_relationship(elm1,elm2,rd);
	}
	
	public static RELATION range_relationship (ELEMENT elm1, ELEMENT elm2, RangeDomain rd){
		
		RangeDomain rd2;
		if(rd == null)
			rd2 = new RangeDomain();
		else 
			rd2 = rd;

		Relation lb_rel,ub_rel,stride_rel;
		Expression elm1_lower, elm1_upper;
		Expression elm2_lower, elm2_upper;
		if(elm1.IsForward()){
			elm1_lower=elm1.getLB(); elm1_upper=elm1.getUB();
		}
		else{
			elm1_lower=elm1.getUB(); elm1_upper=elm1.getLB();
		}
		if( elm2.IsBackward()){
			elm2_lower=elm2.getUB(); elm2_upper=elm2.getLB();
		}
		else{
			elm2_lower=elm2.getLB(); elm2_upper=elm2.getUB();
		}
		lb_rel = rd2.compare(elm1_lower, elm2_lower);
		ub_rel = rd2.compare(elm1_upper, elm2_upper);
		if(lb_rel.isUnknown())
			lb_rel = rd2.compare(Symbolic.subtract(elm1_lower, elm2_lower), new IntegerLiteral(0));
		if(ub_rel.isUnknown())
			ub_rel = rd2.compare(Symbolic.subtract(elm1_upper, elm2_upper), new IntegerLiteral(0));
		
		
		if(lb_rel.isUnknown() && elm1.IsUnitStride() && elm2.IsUnitStride() ){
			//check if we have the case of (x:y:1) and (y-1:y:1)
			// we know x<=y and we know x!=y
			// thus we know x<=(y-1)
			if(ub_rel.isEQ()){
				if(Symbolic.subtract(elm1_upper, elm1_lower).equals(new IntegerLiteral(1))) {
					//if elm1=(y-1:y:1) and elm2=(x:y:1)
					lb_rel.setEQ(true);lb_rel.setGT(true);
				}
				else if(Symbolic.subtract(elm1_upper, elm1_lower).equals(new IntegerLiteral(0))) {
					//if elm1=(y:y:1) and elm2=(x:y:1)
					lb_rel.setGT(true);
				}
				else if(Symbolic.subtract(elm2_upper, elm2_lower).equals(new IntegerLiteral(1))){
					//if elm2=(y-1:y:1) and elm1=(x:y:1)
					lb_rel.setEQ(true);lb_rel.setLT(true);
				}
				else if(Symbolic.subtract(elm2_upper, elm2_lower).equals(new IntegerLiteral(0))){
					//if elm2=(y:y:1) and and elm1=(x:y:1)
					lb_rel.setLT(true);
				}
			}
			else if(Symbolic.subtract(elm2_upper, elm1_upper).equals(new IntegerLiteral(1))){
				if(Symbolic.subtract(elm1_upper, elm1_lower).equals(new IntegerLiteral(0))) {
					//if elm1=(y-1:y-1:1) and elm2=(x:y:1)
					lb_rel.setEQ(true);lb_rel.setGT(true);
				}
			}
			else if(Symbolic.subtract(elm1_upper, elm2_upper).equals(new IntegerLiteral(1))){
				if(Symbolic.subtract(elm2_upper, elm2_lower).equals(new IntegerLiteral(0))) {
					//if elm2=(y-1:y-1:1) and elm1=(x:y:1)
					lb_rel.setEQ(true);lb_rel.setLT(true);
				}
			}
			
		}		
		else if(ub_rel.isUnknown() && elm1.IsUnitStride() && elm2.IsUnitStride() ){
			//check if we have the case of (x:x+1:1) and (x:y:1)
			// we know x<=y and we know x!=y
			// thus we know (x+1)<=y or x<=(y-1)
			if(lb_rel.isEQ()){
				if(Symbolic.subtract(elm1_upper, elm1_lower).equals(new IntegerLiteral(1))) {
					//if elm1=(x:x+1:1) and elm2=(x:y:1)
					ub_rel.setEQ(true); ub_rel.setLT(true);
				}
				else if(Symbolic.subtract(elm1_upper, elm1_lower).equals(new IntegerLiteral(0))) {
					//if elm1=(x:x:1) and elm2=(x:y:1)
					ub_rel.setLT(true);
				} 
				else if(Symbolic.subtract(elm2_upper, elm2_lower).equals(new IntegerLiteral(1))) {
					//if elm2=(x:x+1:1) and elm1=(x:y:1)
					ub_rel.setEQ(true); ub_rel.setGT(true);
				}
				else if(Symbolic.subtract(elm2_upper, elm2_lower).equals(new IntegerLiteral(0))) {
					//if elm2=(x:x:1) and elm1=(x:y:1)
					ub_rel.setGT(true);
				}
			}
			else if(Symbolic.subtract(elm1_lower, elm2_lower).equals(new IntegerLiteral(1))){
				if(Symbolic.subtract(elm1_upper, elm1_lower).equals(new IntegerLiteral(0))) {
					//if elm1=(x+1:x+1:1) and elm2=(x:y:1)
					ub_rel.setEQ(true); ub_rel.setLT(true);
				}
			}
			else if(Symbolic.subtract(elm2_lower, elm1_lower).equals(new IntegerLiteral(1))){
				if(Symbolic.subtract(elm2_upper, elm2_lower).equals(new IntegerLiteral(0))) {
					//if elm2=(x+1:x+1:1) and elm1=(x:y:1)
					ub_rel.setEQ(true); ub_rel.setGT(true);
				}
			}
			 
		}		
		
		/*
		if(lb_rel.isUnknown() && ub_rel.isEQ() && elm1.IsUnitStride() && elm2.IsUnitStride() ){
			//check if we have the case of (x:y:1) and (y-1:y:1)
			// we know x<=y and we know x!=y
			// thus we know x<=(y-1)
			if(Symbolic.subtract(elm1_upper, elm1_lower).equals(new IntegerLiteral(1))) {
				//if elm1=(y-1:y:1)
				lb_rel.setEQ(true);lb_rel.setGT(true);
			}
			else if(Symbolic.subtract(elm1_upper, elm1_lower).equals(new IntegerLiteral(1))){
				//if elm2=(y-1:y:1)
				lb_rel.setEQ(true);lb_rel.setLT(true);
			}
		}
		
		else if(lb_rel.isEQ() && ub_rel.isUnknown() && elm1.IsUnitStride() && elm2.IsUnitStride() ){
			//check if we have the case of (x:x+1:1) and (x:y:1)
			// we know x<=y and we know x!=y
			// thus we know (x+1)<=y or x<=(y-1)
			if(Symbolic.subtract(elm1_upper, elm1_lower).equals(new IntegerLiteral(1))) {
				//if elm1=(x:x+1:1)
				ub_rel.setEQ(true); ub_rel.setLT(true);
			} 
			else if(Symbolic.subtract(elm2_upper, elm2_lower).equals(new IntegerLiteral(1))) {
				//if elm2=(x:x+1:1)
				ub_rel.setEQ(true); ub_rel.setGT(true);
			}
		}
		*/
		
		if(lb_rel.isUnknown() || ub_rel.isUnknown())
			if(rd2.compare(elm1_upper, elm2_lower).isLT() || rd2.compare(elm2_upper, elm1_lower).isLT())
				 return RELATION.INDEPENDENT;
		if(lb_rel.isUnknown() && ub_rel.isUnknown())
			return RELATION.UNKNOWN;
		
		if(lb_rel.isUnknown())
			if(elm1_lower.equals(new IntegerLiteral(0) ))
				{lb_rel.setLT(true); lb_rel.setEQ(true);}
			else if(elm2_lower.equals(new IntegerLiteral(0)))
				{lb_rel.setGT(true); lb_rel.setEQ(true);}
			else if(elm1_lower.equals(elm1.full_size.getUB()))
				{lb_rel.setGT(true); lb_rel.setEQ(true);}
			else if(elm2_lower.equals(elm2.full_size.getUB()))
				{lb_rel.setLT(true); lb_rel.setEQ(true);}
		if(ub_rel.isUnknown())
			if(elm1_upper.equals(new IntegerLiteral(0)))
				{ub_rel.setLT(true); ub_rel.setEQ(true);}
			else if(elm2_upper.equals(new IntegerLiteral(0)))
				{ub_rel.setGT(true); ub_rel.setEQ(true);}
			else if(elm1_upper.equals(elm1.full_size.getUB()))
				{ub_rel.setGT(true); ub_rel.setEQ(true);}
			else if(elm2_upper.equals(elm2.full_size.getUB()))
				{ub_rel.setLT(true); ub_rel.setEQ(true);}

		
		if(lb_rel.isEQ() && ub_rel.isEQ()){
			if(elm1.IsForward() && elm2.IsForward()){
				stride_rel = rd2.compare(elm1.getSTRIDE(), elm2.getSTRIDE());
				if(stride_rel.isUnknown())
					if(elm1.getSTRIDE().equals(elm2.getSTRIDE()))
						stride_rel.setEQ(true);
				if(stride_rel.isEQ())
					return RELATION.EQUAL;
			}
			else if(elm1.IsForward() && elm2.IsBackward()){
				stride_rel = rd2.compare(elm1.getSTRIDE(), Symbolic.multiply(new IntegerLiteral(-1), elm2.getSTRIDE()));
				if(stride_rel.isUnknown())
					if(elm1.getSTRIDE().equals(Symbolic.multiply(new IntegerLiteral(-1), elm2.getSTRIDE())))
						stride_rel.setEQ(true);
				if(stride_rel.isEQ())
					return RELATION.EQUAL;
			}
			else if(elm1.IsBackward() && elm2.IsForward()){
				stride_rel = rd2.compare(Symbolic.multiply(new IntegerLiteral(-1), elm1.getSTRIDE()), elm2.getSTRIDE());
				if(stride_rel.isUnknown())
					if(elm2.getSTRIDE().equals(Symbolic.multiply(new IntegerLiteral(-1), elm1.getSTRIDE())))
						stride_rel.setEQ(true);
				if(stride_rel.isEQ())
					return RELATION.EQUAL;
			}
			else{
				stride_rel = rd2.compare(Symbolic.multiply(new IntegerLiteral(-1), elm1.getSTRIDE()), Symbolic.multiply(new IntegerLiteral(-1), elm2.getSTRIDE()));
				if(stride_rel.isUnknown())
					if(Symbolic.multiply(new IntegerLiteral(-1), elm2.getSTRIDE()).equals(Symbolic.multiply(new IntegerLiteral(-1), elm1.getSTRIDE())))
						stride_rel.setEQ(true);
				if(stride_rel.isEQ())
					return RELATION.EQUAL;
			}
		}

		if(rd2.compare(elm1_upper, elm2_lower).isLT() || rd2.compare(elm2_upper, elm1_lower).isLT())
			 return RELATION.INDEPENDENT;
		
		if(elm1.IsUnitStride() && elm2.IsUnitStride() ){ // common case
			 if(lb_rel.isLE() && ub_rel.isGE())
				 return RELATION.SUBSUMES;
			 if(lb_rel.isGE() && ub_rel.isLE())
				 return RELATION.SUBSETOF;
			 /*if(rd2.compare(elm1.getUB(), elm2.getLB()).isGE() && ub_rel.isLE())
				 return RELATION.OVERLAP;
			 if(rd2.compare(elm2.getUB(), elm1.getLB()).isGE() && ub_rel.isGE())
				 return RELATION.OVERLAP;*/
			 if(lb_rel.isGE() && ub_rel.isGE())
				 return RELATION.OVERLAP;
			 if(lb_rel.isLE() && ub_rel.isLE())
				 return RELATION.OVERLAP;
			 return RELATION.UNKNOWN; 
		}
		else if(elm1.IsTwoStride() && elm2.IsTwoStride() ){
			Expression mod;
			if(lb_rel.isLE())
				mod = Symbolic.mod(Symbolic.subtract(elm2_lower, elm1_lower), new IntegerLiteral(2));
			else
				mod = Symbolic.mod(Symbolic.subtract(elm1_lower, elm2_lower), new IntegerLiteral(2));
			
			if(rd2.compare(mod, new IntegerLiteral(1)).isEQ())
				return RELATION.INDEPENDENT;
			if(rd2.compare(mod, new IntegerLiteral(1)).isEQ())
				return RELATION.UNKNOWN;
			
			if(lb_rel.isLE() && ub_rel.isGE())
				 return RELATION.SUBSUMES;
			 if(lb_rel.isGE() && ub_rel.isLE())
				 return RELATION.SUBSETOF;
			 if(lb_rel.isGE() && ub_rel.isGE())
				 return RELATION.OVERLAP;
			 if(lb_rel.isLE() && ub_rel.isLE())
				 return RELATION.OVERLAP;
			 return RELATION.UNKNOWN;
			
		}
		else if(elm1.IsTwoStride() && elm2.IsUnitStride() ){
			if(lb_rel.isGE() && ub_rel.isLE())
				 return RELATION.SUBSETOF;
			if(lb_rel.isLE() && ub_rel.isGE()){
				if(rd2.compare(elm2_lower, elm2_upper).isEQ() && (lb_rel.isEQ() || ub_rel.isEQ()))
					return RELATION.SUBSUMES;
				else
					return RELATION.UNKNOWN;
			}
			if(lb_rel.isGE() && ub_rel.isGE())
				 return RELATION.OVERLAP;
			 if(lb_rel.isLE() && ub_rel.isLE())
				 return RELATION.OVERLAP;
			 return RELATION.UNKNOWN; 
		}
		else if(elm1.IsUnitStride() && elm2.IsTwoStride() ){
			if(lb_rel.isGE() && ub_rel.isLE()){
				 if(rd2.compare(elm1_lower, elm1_upper).isEQ() && (lb_rel.isEQ() || ub_rel.isEQ()))
					 return RELATION.SUBSETOF;
				 else
					 return RELATION.UNKNOWN;
			}
			if(lb_rel.isLE() && ub_rel.isGE())
				 return RELATION.SUBSUMES;
			if(lb_rel.isGE() && ub_rel.isGE())
				 return RELATION.OVERLAP;
			 if(lb_rel.isLE() && ub_rel.isLE())
				 return RELATION.OVERLAP;
			 return RELATION.UNKNOWN; 
		}
		
		return RELATION.UNKNOWN;
	}

/** return true if elm1 is a subset of elm2 */
	public static BOOLEAN IsSubsetOf(ELEMENT elm1, ELEMENT elm2, RangeDomain rd){
		RELATION rel = ELEMENT.relationship(elm1, elm2, rd);
		if(rel.equals(RELATION.UNKNOWN))
			return BOOLEAN.UNKNOWN;
		if(rel.equals(RELATION.SUBSETOF) || rel.equals(RELATION.EQUAL))
			return BOOLEAN.TRUE;
		return BOOLEAN.FALSE;
	}
	
	public static boolean isSubsetOf(ELEMENT elm1, ELEMENT elm2, RangeDomain rd){
    	return ELEMENT.IsSubsetOf(elm1,elm2, rd).equals(BOOLEAN.TRUE);
    }

/** return true if elm1 is equal to elm2 */
	public static BOOLEAN IsEqual(ELEMENT elm1, ELEMENT elm2, RangeDomain rd){
		RELATION rel = ELEMENT.relationship(elm1, elm2, rd);
		if(rel.equals(RELATION.UNKNOWN))
			return BOOLEAN.UNKNOWN;
		if(rel.equals(RELATION.EQUAL))
			return BOOLEAN.TRUE;
		return BOOLEAN.FALSE;
	}
	
	public static boolean isEqual(ELEMENT elm1, ELEMENT elm2, RangeDomain rd){
    	return ELEMENT.IsEqual(elm1,elm2, rd).equals(BOOLEAN.TRUE);
    }
	
/** return true if elm1 does not overlap with elm2 */
	public static BOOLEAN IsIndependent(ELEMENT elm1, ELEMENT elm2, RangeDomain rd){
		RELATION rel = ELEMENT.relationship(elm1, elm2, rd);
		if(rel.equals(RELATION.UNKNOWN)){
			RangeDomain rd1;
			if(rd==null) rd1=new RangeDomain(); else rd1=rd;
			if(    rd1.isEQ(elm1.getLB(), elm2.getLB()) // check if there is at least one common element on borders
				|| rd1.isEQ(elm1.getLB(), elm2.getUB()) 
				|| rd1.isEQ(elm1.getUB(), elm2.getLB())
				|| rd1.isEQ(elm1.getUB(), elm2.getUB()))
				return BOOLEAN.FALSE;
			return BOOLEAN.UNKNOWN;
		}
		if(rel.equals(RELATION.INDEPENDENT))
			return BOOLEAN.TRUE;
		return BOOLEAN.FALSE;
	}
	
	public static boolean isIndependent(ELEMENT elm1, ELEMENT elm2, RangeDomain rd){
    	return ELEMENT.IsIndependent(elm1,elm2, rd).equals(BOOLEAN.TRUE);
    }
	
/*returns true if the distance between two independent elements is exactly 1  */
	public static boolean IsNeighbour(ELEMENT elm1, ELEMENT elm2, RangeDomain rd1){
		RangeDomain rd;
		if(rd1==null)
			rd=new RangeDomain();
		else rd=rd1;
		//assert(ELEMENT.IsIndependent(elm1, elm2, rd)==true);
		
		Expression elm1_lower, elm1_upper;
		Expression elm2_lower, elm2_upper;
		if(elm1.IsForward()){
			elm1_lower=elm1.getLB(); elm1_upper=elm1.getUB();
		}
		else{
			elm1_lower=elm1.getUB(); elm1_upper=elm1.getLB();
		}
		if( elm2.IsBackward()){
			elm2_lower=elm2.getUB(); elm2_upper=elm2.getLB();
		}
		else{
			elm2_lower=elm2.getLB(); elm2_upper=elm2.getUB();
		}
				
		if(elm1.IsUnitStride() && elm2.IsUnitStride()){ //common case
			/*if(elm1.IsForward() && elm2.IsForward()){
				if(Symbolic.subtract(elm2.getLB(), elm1.getUB()).equals(new IntegerLiteral(1)))
					return true;
				if(Symbolic.subtract(elm1.getLB(), elm2.getUB()).equals(new IntegerLiteral(1)))
					return true;
			}
			else if(elm1.IsForward() && elm2.IsBackward()){
				if(Symbolic.subtract(elm2.getUB(), elm1.getUB()).equals(new IntegerLiteral(1)))
					return true;
				if(Symbolic.subtract(elm1.getLB(), elm2.getLB()).equals(new IntegerLiteral(1)))
					return true;
			}
			else if(elm1.IsBackward() && elm2.IsForward()){
				if(Symbolic.subtract(elm2.getLB(), elm1.getLB()).equals(new IntegerLiteral(1)))
					return true;
				if(Symbolic.subtract(elm1.getUB(), elm2.getUB()).equals(new IntegerLiteral(1)))
					return true;
			}
			else{ //elm1.IsBackward() && elm2.IsBackward() 
				if(Symbolic.subtract(elm2.getUB(), elm1.getLB()).equals(new IntegerLiteral(1)))
					return true;
				if(Symbolic.subtract(elm1.getUB(), elm2.getLB()).equals(new IntegerLiteral(1)))
					return true;
			}*/
			if(Symbolic.subtract(elm2_lower, elm1_upper).equals(new IntegerLiteral(1)))
				return true;
			if(Symbolic.subtract(elm1_lower, elm2_upper).equals(new IntegerLiteral(1)))
				return true;
			return false;
		}
		
		if(elm1.IsTwoStride() && elm2.IsTwoStride()){
			if(Symbolic.subtract(elm1_lower, elm2_lower).equals(new IntegerLiteral(1)))
				return true;
			if(Symbolic.subtract(elm2_lower, elm1_lower).equals(new IntegerLiteral(1)))
				return true;
			if(Symbolic.subtract(elm2_lower, elm1_upper).equals(new IntegerLiteral(2)))
				return true;
			if(Symbolic.subtract(elm1_lower, elm2_upper).equals(new IntegerLiteral(2)))
				return true;
			return false;
		}
		
		if(elm1.IsUnitStride() && elm2.IsTwoStride() && elm2.getLB().equals(elm2.getUB())
		|| (elm2.IsUnitStride() && elm1.IsTwoStride() && elm1.getLB().equals(elm1.getUB())) ){
			if(Symbolic.subtract(elm2_lower, elm1_upper).equals(new IntegerLiteral(1)))
				return true;
			if(Symbolic.subtract(elm1_lower, elm2_upper).equals(new IntegerLiteral(1)))
				return true;
			return false;
		}
		
		return false;
	}
	
	public static ELEMENT intersect (ELEMENT elm1, ELEMENT elm2, RangeDomain rd){

		/*if(elm1 == null && elm2 == null)
			return null;*/
		if(elm1 == null || elm2 == null || elm1.isEmpty() || elm2.isEmpty())
			return new ELEMENT();
		RELATION rel = relationship(elm1,elm2,rd);
		if(rel.equals(RELATION.EQUAL) || rel.equals(RELATION.SUBSETOF))
			return elm1.clone();
		if(rel.equals(RELATION.SUBSUMES))
			return elm2.clone();
		if(rel.equals(RELATION.INDEPENDENT))
			return new ELEMENT();
		if(rel.equals(RELATION.OVERLAP)){
			ELEMENT tmp = elm1.intersect_overlapping_elements(elm2, rd);
			tmp.set_full_size_element(elm1.full_size);
			return tmp;
		}
		return null;
	}
	
	private ELEMENT intersect_overlapping_elements(ELEMENT elm, RangeDomain rd){
		RangeDomain rd2;
		if(rd == null)
			rd2 = new RangeDomain();
		else 
			rd2 = rd;
		if(this.IsUnitStride() || elm.IsUnitStride()){ //common case
			if(this.IsForward() && elm.IsForward()){
				Relation rel1 = rd2.compare(this.getLB(), elm.getLB());
//				Relation rel2 = rd2.compare(this.getUB(), elm.getUB()); // I know that rel2 will correspond to rel1
				if(rel1.isLE())
					return new ELEMENT(elm.getLB().clone(),this.getUB().clone(),new IntegerLiteral(1));
				else
					return new ELEMENT(this.getLB().clone(),elm.getUB().clone(),new IntegerLiteral(1));
			}
			else if(this.IsForward() && elm.IsBackward()){
				Relation rel1 = rd2.compare(this.getLB(), elm.getUB());
				if(rel1.isLE())
					return new ELEMENT(elm.getUB().clone(),this.getUB().clone(),new IntegerLiteral(1));
				else
					return new ELEMENT(this.getLB().clone(),elm.getLB().clone(),new IntegerLiteral(1));
			}
			else if(this.IsBackward() && elm.IsForward()){
				Relation rel1 = rd2.compare(this.getUB(), elm.getLB());
				if(rel1.isLE())
					return new ELEMENT(elm.getLB().clone(),this.getLB().clone(),new IntegerLiteral(1));
				else
					return new ELEMENT(this.getUB().clone(),elm.getUB().clone(),new IntegerLiteral(1));
			}
			else{ //this.IsBackward() && elm.IsBackward() 
				Relation rel1 = rd2.compare(this.getUB(), elm.getUB());
				if(rel1.isLE())
					return new ELEMENT(this.getLB().clone(),elm.getUB().clone(),new IntegerLiteral(-1));
				else
					return new ELEMENT(elm.getLB().clone(),this.getUB().clone(),new IntegerLiteral(-1));
			}
		}
		else if(this.IsTwoStride() || elm.IsTwoStride()){
			if(this.IsForward() && elm.IsForward()){
				Relation rel1 = rd2.compare(this.getLB(), elm.getLB());
//				Relation rel2 = rd2.compare(this.getUB(), elm.getUB()); // I know that rel2 will correspond to rel1
				if(rel1.isLE())
					return new ELEMENT(elm.getLB().clone(),this.getUB().clone(),new IntegerLiteral(2));
				else
					return new ELEMENT(this.getLB().clone(),elm.getUB().clone(),new IntegerLiteral(2));
			}
			else if(this.IsForward() && elm.IsBackward()){
				Relation rel1 = rd2.compare(this.getLB(), elm.getUB());
				if(rel1.isLE())
					return new ELEMENT(elm.getUB().clone(),this.getUB().clone(),new IntegerLiteral(2));
				else
					return new ELEMENT(this.getLB().clone(),elm.getLB().clone(),new IntegerLiteral(2));
			}
			else if(this.IsBackward() && elm.IsForward()){
				Relation rel1 = rd2.compare(this.getUB(), elm.getLB());
				if(rel1.isLE())
					return new ELEMENT(elm.getLB().clone(),this.getLB().clone(),new IntegerLiteral(2));
				else
					return new ELEMENT(this.getUB().clone(),elm.getUB().clone(),new IntegerLiteral(2));
			}
			else{ //this.IsBackward() && elm.IsBackward() 
				Relation rel1 = rd2.compare(this.getUB(), elm.getUB());
				if(rel1.isLE())
					return new ELEMENT(this.getLB().clone(),elm.getUB().clone(),new IntegerLiteral(-2));
				else
					return new ELEMENT(elm.getLB().clone(),this.getUB().clone(),new IntegerLiteral(-2));
			}
		}
		else if(this.getSTRIDE().equals(elm.getSTRIDE())){
			if(this.IsForward() && elm.IsForward()){
				Relation rel1 = rd2.compare(this.getLB(), elm.getLB());
//				Relation rel2 = rd2.compare(this.getUB(), elm.getUB()); // I know that rel2 will correspond to rel1
				if(rel1.isLE())
					return new ELEMENT(elm.getLB().clone(),this.getUB().clone(),this.getSTRIDE().clone());
				else
					return new ELEMENT(this.getLB().clone(),elm.getUB().clone(),this.getSTRIDE().clone());
			}
			else if(this.IsForward() && elm.IsBackward()){
				Relation rel1 = rd2.compare(this.getLB(), elm.getUB());
				if(rel1.isLE())
					return new ELEMENT(elm.getUB().clone(),this.getUB().clone(),this.getSTRIDE().clone());
				else
					return new ELEMENT(this.getLB().clone(),elm.getLB().clone(),this.getSTRIDE().clone());
			}
			else if(this.IsBackward() && elm.IsForward()){
				Relation rel1 = rd2.compare(this.getUB(), elm.getLB());
				if(rel1.isLE())
					return new ELEMENT(elm.getLB().clone(),this.getLB().clone(),elm.getSTRIDE().clone());
				else
					return new ELEMENT(this.getUB().clone(),elm.getUB().clone(),elm.getSTRIDE().clone());
			}
			else{ //this.IsBackward() && elm.IsBackward() 
				Relation rel1 = rd2.compare(this.getUB(), elm.getUB());
				if(rel1.isLE())
					return new ELEMENT(this.getLB().clone(),elm.getUB().clone(),this.getSTRIDE().clone());
				else
					return new ELEMENT(elm.getLB().clone(),this.getUB().clone(),this.getSTRIDE().clone());
			}
		}
		
		return null;
	}
	
	public static ELEMENT union (ELEMENT elm1, ELEMENT elm2, RangeDomain rd){
		assert(elm1!=null || elm2!=null );
		if(elm1==null)
			return elm2.clone();
		if(elm1.isEmpty())
			return elm2.clone();
		if(elm2==null)
			return elm1.clone();
		if(elm2.isEmpty())
			return elm1.clone();
		if(elm1.IsInfiniteElement() && elm2.IsInfiniteElement())
			return elm1.clone(); 
		
		RELATION rel = relationship(elm1,elm2,rd);
		if(rel.equals(RELATION.EQUAL) || rel.equals(RELATION.SUBSUMES))
			return elm1.clone();
		if(rel.equals(RELATION.SUBSETOF))
			return elm2.clone();
		if(rel.equals(RELATION.OVERLAP)){
			ELEMENT tmp = elm1.union_overlapping_elements(elm2,rd);
			if(tmp==null)
				return null;
			tmp.set_full_size_element(elm1.full_size);
			return tmp;
		}
		if(rel.equals(RELATION.INDEPENDENT)){
			ELEMENT tmp = elm1.union_independent_elements(elm2, rd);
			if(tmp==null)
				return null;
			tmp.set_full_size_element(elm1.full_size);
			return tmp;
		}
		//unknow relationship, conservatevily return [-INF:+INF:1]
		//return new ELEMENT(new InfExpression(-1),new InfExpression(+1),new IntegerLiteral(1));
		return null;
	}
	
	private ELEMENT union_overlapping_elements(ELEMENT elm, RangeDomain rd){
		RangeDomain rd2;
		if(rd == null)
			rd2 = new RangeDomain();
		else 
			rd2 = rd;
		if(this.IsUnitStride() && elm.IsUnitStride()){ //common case
			if(this.IsForward() && elm.IsForward()){
				Relation rel1 = rd2.compare(this.getLB(), elm.getLB());
//				Relation rel2 = rd2.compare(this.getUB(), elm.getUB()); // I know that rel2 will correspond to rel1
				if(rel1.isLE())
					return new ELEMENT(this.getLB().clone(),elm.getUB().clone(),new IntegerLiteral(1));
				else 
					return new ELEMENT(elm.getLB().clone(),this.getUB().clone(),new IntegerLiteral(1));
			}
			else if(this.IsForward() && elm.IsBackward()){
				Relation rel1 = rd2.compare(this.getLB(), elm.getUB());
				if(rel1.isLE())
					return new ELEMENT(this.getLB().clone(),elm.getLB().clone(),new IntegerLiteral(1));
				else 
					return new ELEMENT(elm.getUB().clone(),this.getUB().clone(),new IntegerLiteral(1));
			}
			else if(this.IsBackward() && elm.IsForward()){
				Relation rel1 = rd2.compare(this.getUB(), elm.getLB());
				if(rel1.isLE())
					return new ELEMENT(this.getUB().clone(),elm.getUB().clone(),new IntegerLiteral(1));
				else 
					return new ELEMENT(elm.getLB().clone(),this.getLB().clone(),new IntegerLiteral(1));
			}
			else{ //this.IsBackward() && elm.IsBackward() 
				Relation rel1 = rd2.compare(this.getUB(), elm.getUB());
				if(rel1.isLE())
					return new ELEMENT(elm.getLB().clone(),this.getUB().clone(),new IntegerLiteral(-1));
				else 
					return new ELEMENT(this.getLB().clone(),elm.getUB().clone(),new IntegerLiteral(-1));
			}
		}
		else if(this.IsTwoStride() && elm.IsTwoStride()){
			if(this.IsForward() && elm.IsForward()){
				Relation rel1 = rd2.compare(this.getLB(), elm.getLB());
//				Relation rel2 = rd2.compare(this.getUB(), elm.getUB()); // I know that rel2 will correspond to rel1
				if(rel1.isLE())
					return new ELEMENT(this.getLB().clone(),elm.getUB().clone(),new IntegerLiteral(2));
				else 
					return new ELEMENT(elm.getLB().clone(),this.getUB().clone(),new IntegerLiteral(2));
			}
			else if(this.IsForward() && elm.IsBackward()){
				Relation rel1 = rd2.compare(this.getLB(), elm.getUB());
				if(rel1.isLE())
					return new ELEMENT(this.getLB().clone(),elm.getLB().clone(),new IntegerLiteral(2));
				else 
					return new ELEMENT(elm.getUB().clone(),this.getUB().clone(),new IntegerLiteral(2));
			}
			else if(this.IsBackward() && elm.IsForward()){
				Relation rel1 = rd2.compare(this.getUB(), elm.getLB());
				if(rel1.isLE())
					return new ELEMENT(this.getUB().clone(),elm.getUB().clone(),new IntegerLiteral(2));
				else 
					return new ELEMENT(elm.getLB().clone(),this.getLB().clone(),new IntegerLiteral(2));
			}
			else{ //this.IsBackward() && elm.IsBackward() 
				Relation rel1 = rd2.compare(this.getUB(), elm.getUB());
				if(rel1.isLE())
					return new ELEMENT(elm.getLB().clone(),this.getUB().clone(),new IntegerLiteral(-2));
				else 
					return new ELEMENT(this.getLB().clone(),elm.getUB().clone(),new IntegerLiteral(-2));
			}
		}
		return null;

	}
	// this basically used to union neighbour elements
	private ELEMENT union_independent_elements(ELEMENT elm, RangeDomain rd){
		RangeDomain rd2;
		if(rd == null)
			rd2 = new RangeDomain();
		else 
			rd2 = rd;
		if(this.IsUnitStride() || elm.IsUnitStride()){ //common case
			if(this.IsForward() && elm.IsForward()){
				Relation rel1 = rd2.compare(this.getUB(), elm.getLB());
				if(rel1.isLE())
					return new ELEMENT(this.getLB().clone(),elm.getUB().clone(),new IntegerLiteral(1));
				else
					return new ELEMENT(elm.getLB().clone(),this.getUB().clone(),new IntegerLiteral(1));
			}
			else if(this.IsForward() && elm.IsBackward()){
				Relation rel1 = rd2.compare(this.getUB(), elm.getUB());
				if(rel1.isLE())
					return new ELEMENT(this.getLB().clone(),elm.getLB().clone(),new IntegerLiteral(1));
				else
					return new ELEMENT(elm.getUB().clone(),this.getUB().clone(),new IntegerLiteral(1));
			}
			else if(this.IsBackward() && elm.IsForward()){
				Relation rel1 = rd2.compare(this.getUB(), elm.getLB());
				if(rel1.isLE())
					return new ELEMENT(this.getUB().clone(),elm.getUB().clone(),new IntegerLiteral(1));
				else
					return new ELEMENT(elm.getLB().clone(),this.getLB().clone(),new IntegerLiteral(1));
			}
			else{ //this.IsBackward() && elm.IsBackward() 
				Relation rel1 = rd2.compare(this.getUB(), elm.getLB());
				if(rel1.isLE())
					return new ELEMENT(elm.getLB().clone(),this.getUB().clone(),new IntegerLiteral(-1));
				else
					return new ELEMENT(this.getLB().clone(),elm.getUB().clone(),new IntegerLiteral(-1));
			}
		}
		else if(this.IsTwoStride() && elm.IsTwoStride()){
			if(this.IsForward() && elm.IsForward()){
				if(Symbolic.subtract(this.getLB(), elm.getLB()).equals(new IntegerLiteral(1))){
					Relation rel1 = rd2.compare(this.getUB(), elm.getUB());
					if(rel1.isUnknown()) return null;
					if(rel1.isLE())
						return new ELEMENT(elm.getLB().clone(),elm.getUB().clone(),new IntegerLiteral(1));
					else
						return new ELEMENT(elm.getLB().clone(),this.getUB().clone(),new IntegerLiteral(1));
				}
				else if(Symbolic.subtract(elm.getLB(), this.getLB()).equals(new IntegerLiteral(1))){
					Relation rel1 = rd2.compare(this.getUB(), elm.getUB());
					if(rel1.isUnknown()) return null;
					if(rel1.isLE())
						return new ELEMENT(this.getLB().clone(),elm.getUB().clone(),new IntegerLiteral(1));
					else
						return new ELEMENT(this.getLB().clone(),this.getUB().clone(),new IntegerLiteral(1));
				}
				else{
					Relation rel1 = rd2.compare(this.getUB(), elm.getLB());
					if(rel1.isUnknown()) return null;
					if(rel1.isLE())
						return new ELEMENT(this.getLB().clone(),elm.getUB().clone(),new IntegerLiteral(2));
					else
						return new ELEMENT(elm.getLB().clone(),this.getUB().clone(),new IntegerLiteral(2));
				}
			}
			else if(this.IsForward() && elm.IsBackward()){
				if(Symbolic.subtract(this.getLB(), elm.getUB()).equals(new IntegerLiteral(1))){
					Relation rel1 = rd2.compare(this.getUB(), elm.getLB());
					if(rel1.isUnknown()) return null;
					if(rel1.isLE())
						return new ELEMENT(elm.getUB().clone(),elm.getLB().clone(),new IntegerLiteral(1));
					else
						return new ELEMENT(elm.getUB().clone(),this.getUB().clone(),new IntegerLiteral(1));
				}
				else if(Symbolic.subtract(elm.getUB(), this.getLB()).equals(new IntegerLiteral(1))){
					Relation rel1 = rd2.compare(this.getUB(), elm.getLB());
					if(rel1.isUnknown()) return null;
					if(rel1.isLE())
						return new ELEMENT(this.getLB().clone(),elm.getLB().clone(),new IntegerLiteral(1));
					else
						return new ELEMENT(this.getLB().clone(),this.getUB().clone(),new IntegerLiteral(1));
				}
				else{
					Relation rel1 = rd2.compare(this.getUB(), elm.getUB());
					if(rel1.isUnknown()) return null;
					if(rel1.isLE())
						return new ELEMENT(this.getLB().clone(),elm.getLB().clone(),new IntegerLiteral(2));
					else
						return new ELEMENT(elm.getUB().clone(),this.getUB().clone(),new IntegerLiteral(2));
				}
			}
			else if(this.IsBackward() && elm.IsForward()){
				if(Symbolic.subtract(this.getUB(), elm.getLB()).equals(new IntegerLiteral(1))){
					Relation rel1 = rd2.compare(this.getLB(), elm.getUB());
					if(rel1.isUnknown()) return null;
					if(rel1.isLE())
						return new ELEMENT(elm.getLB().clone(),elm.getUB().clone(),new IntegerLiteral(1));
					else
						return new ELEMENT(elm.getLB().clone(),this.getLB().clone(),new IntegerLiteral(1));
				}
				else if(Symbolic.subtract(elm.getLB(), this.getUB()).equals(new IntegerLiteral(1))){
					Relation rel1 = rd2.compare(this.getLB(), elm.getUB());
					if(rel1.isUnknown()) return null;
					if(rel1.isLE())
						return new ELEMENT(this.getUB().clone(),elm.getUB().clone(),new IntegerLiteral(1));
					else
						return new ELEMENT(this.getUB().clone(),this.getLB().clone(),new IntegerLiteral(1));
				}
				else{
					Relation rel1 = rd2.compare(this.getLB(), elm.getLB());
					if(rel1.isUnknown()) return null;
					if(rel1.isLE())
						return new ELEMENT(this.getUB().clone(),elm.getUB().clone(),new IntegerLiteral(2));
					else
						return new ELEMENT(elm.getLB().clone(),this.getLB().clone(),new IntegerLiteral(2));
				}
			}
			else if(this.IsBackward() && elm.IsBackward()){
				if(Symbolic.subtract(this.getUB(), elm.getUB()).equals(new IntegerLiteral(1))){
					Relation rel1 = rd2.compare(this.getLB(), elm.getLB());
					if(rel1.isUnknown()) return null;
					if(rel1.isLE())
						return new ELEMENT(elm.getLB().clone(),elm.getUB().clone(),new IntegerLiteral(-1));
					else
						return new ELEMENT(this.getLB().clone(),elm.getUB().clone(),new IntegerLiteral(-1));
				}
				if(Symbolic.subtract(elm.getUB(), this.getUB()).equals(new IntegerLiteral(1))){
					Relation rel1 = rd2.compare(this.getLB(), elm.getLB());
					if(rel1.isUnknown()) return null;
					if(rel1.isLE())
						return new ELEMENT(elm.getLB().clone(),this.getUB().clone(),new IntegerLiteral(-1));
					else
						return new ELEMENT(this.getLB().clone(),this.getUB().clone(),new IntegerLiteral(-1));
				}
				else{
					Relation rel1 = rd2.compare(this.getLB(), elm.getUB());
					if(rel1.isUnknown()) return null;
					if(rel1.isLE())
						return new ELEMENT(elm.getLB().clone(),this.getUB().clone(),new IntegerLiteral(-2));
					else
						return new ELEMENT(this.getLB().clone(),elm.getUB().clone(),new IntegerLiteral(-2));
				}
			}
		}
		
		return null;	
	}
	
	//this function assumes elm1 subsumes elm2
	public static ArrayList<ELEMENT> subtract (ELEMENT elm1, ELEMENT elm2, RangeDomain rd){
		if(elm1.IsInfiniteElement()){
			ArrayList<ELEMENT> tmp = new ArrayList<ELEMENT>();
			tmp.add(elm1.clone());
			return tmp;
		}
		if(elm2.IsInfiniteElement()){
			return new ArrayList<ELEMENT>();
		}
		if(ELEMENT.IsEqual(elm1, elm2, rd).equals(BOOLEAN.TRUE))
			return new ArrayList<ELEMENT>();
		ArrayList<ELEMENT> tmp = elm1.subtract_smaller_from_me(elm2,rd);
		if(tmp==null){
			//ArrayList<ELEMENT> tmp1 = new ArrayList<ELEMENT>();
			//tmp1.add(elm1.clone());
			//return tmp1;
			return null;
		}
		for(ELEMENT e:tmp)
			e.set_full_size_element(elm1.full_size);
		return tmp;
	}
	
	private ArrayList<ELEMENT> subtract_smaller_from_me(ELEMENT elm, RangeDomain rd){
		RangeDomain rd2;
		if(rd == null)
			rd2 = new RangeDomain();
		else 
			rd2 = rd;
		Expression this_lower, this_upper;
		Expression elm_lower, elm_upper;
		if(this.IsForward() && elm.IsForward()){
			this_lower=this.getLB(); this_upper=this.getUB();
			elm_lower=elm.getLB(); elm_upper=elm.getUB();
		}
		else if(this.IsForward() && elm.IsBackward()){
			this_lower=this.getLB(); this_upper=this.getUB();
			elm_lower=elm.getUB(); elm_upper=elm.getLB();
		}
		else if(this.IsBackward() && elm.IsForward()){
			this_lower=this.getUB(); this_upper=this.getLB();
			elm_lower=elm.getLB(); elm_upper=elm.getUB();
		}
		else{ //this.IsBackward() && elm.IsBackward() 
			this_lower=this.getUB(); this_upper=this.getLB();
			elm_lower=elm.getUB(); elm_upper=elm.getLB();
		}
		Relation rel1 = rd2.compare(this_lower, elm_lower);
		if(rel1.isLE()){
			if(this_lower instanceof Identifier && rd.getRange(SymbolTools.getSymbolOf(this_lower))!=null && rd.getRange(SymbolTools.getSymbolOf(this_lower)) instanceof RangeExpression && rd.compare( ((RangeExpression)rd.getRange(SymbolTools.getSymbolOf(this_lower))).getUB(), elm_lower).isEQ() )
				rel1 = new Relation(true,false,false); // make rel1 = LT
			if(elm_lower instanceof Identifier && rd.getRange(SymbolTools.getSymbolOf(elm_lower))!=null && rd.getRange(SymbolTools.getSymbolOf(elm_lower)) instanceof RangeExpression && rd.compare( ((RangeExpression)rd.getRange(SymbolTools.getSymbolOf(elm_lower))).getLB(), this_lower).isEQ() )
				rel1 = new Relation(true,false,false); // make rel1 = LT
		}
		Relation rel2 = rd2.compare(this_upper, elm_upper);
		if(rel2.isGE()){
			if(elm_upper instanceof Identifier && rd.getRange(SymbolTools.getSymbolOf(elm_upper))!=null && rd.getRange(SymbolTools.getSymbolOf(elm_upper)) instanceof RangeExpression && rd.compare( ((RangeExpression)rd.getRange(SymbolTools.getSymbolOf(elm_upper))).getUB(), this_upper).isEQ() )
				rel2 = new Relation(false,false,true); // make rel1 = GT
			//if(this_upper instanceof Identifier && rd.getRange(SymbolTools.getSymbolOf(this_upper))!=null && rd.getRange(SymbolTools.getSymbolOf(this_upper)) instanceof RangeExpression && rd.compare( ((RangeExpression)rd.getRange(SymbolTools.getSymbolOf(this_upper))).getUB(), elm_upper).isEQ() )
			//	rel2 = new Relation(false,false,true); // make rel1 = GT
		}
		
		if(this.IsUnitStride() && elm.IsUnitStride()){
			ArrayList<ELEMENT> tmp = new ArrayList<ELEMENT>();
			if(rel1.isLT() && rel2.isGT()){
				tmp.add(new ELEMENT(this_lower.clone(),Symbolic.subtract(elm_lower,new IntegerLiteral(1)),new IntegerLiteral(1)));
				tmp.add(new ELEMENT(Symbolic.add(elm_upper,new IntegerLiteral(1)),this_upper.clone(),new IntegerLiteral(1)));
			}
			else if(rel1.isLT() && rel2.isEQ())
				tmp.add(new ELEMENT(this_lower.clone(),Symbolic.subtract(elm_lower,new IntegerLiteral(1)),new IntegerLiteral(1)));
			else if(rel1.isEQ() && rel2.isGT())
				tmp.add(new ELEMENT(Symbolic.add(elm_upper,new IntegerLiteral(1)),this_upper.clone(),new IntegerLiteral(1)));
			if(tmp.isEmpty())
				return null;
			return tmp;
		}
		else if(this.IsTwoStride() && elm.IsTwoStride()){
			ArrayList<ELEMENT> tmp = new ArrayList<ELEMENT>();
			if(rel1.isLT() && rel2.isGT()){
				tmp.add(new ELEMENT(this_lower.clone(),Symbolic.subtract(elm_lower,new IntegerLiteral(2)),new IntegerLiteral(2)));
				tmp.add(new ELEMENT(Symbolic.add(elm_upper,new IntegerLiteral(2)),this_upper.clone(),new IntegerLiteral(2)));
			}
			else if(rel1.isLT() && rel2.isEQ())
				tmp.add(new ELEMENT(this_lower.clone(),Symbolic.subtract(elm_lower,new IntegerLiteral(2)),new IntegerLiteral(2)));
			else if(rel1.isEQ() && rel2.isGT())
				tmp.add(new ELEMENT(Symbolic.add(elm_upper,new IntegerLiteral(2)),this_upper.clone(),new IntegerLiteral(2)));
			if(tmp.isEmpty())
				return null;
			return tmp;
			
		}
		
		return null;
	}
	
private enum SECTION_ACCESS{
		parallel, serial;
	}

private enum DIRECTION{
	 	FORWARD, //stride is positive
	 	BACKWARD //stirde is negative
	}

} // end of SectionSet.ELEMENT

private enum RELATION{
	EQUAL, SUBSUMES, SUBSETOF, OVERLAP, INDEPENDENT, UNKNOWN;
}

public static class MAP extends HashMap<Symbol,SectionSet> implements Cloneable{
	
	private static final long serialVersionUID = 14L;

	public MAP()
    {
      super();
    }
	public MAP(Symbol s, SectionSet set)
	{
		super();
		this.put(s, set);
	}
	public MAP clone(){
		SectionSet.MAP tmp = new MAP();
		for(Symbol s:this.keySet()){
			tmp.put(s,this.get(s).clone());
		}
		return tmp;
	}
	public String toString(){
		String tmp="{";
		for(Symbol s:this.keySet()){
			tmp=tmp+s.getSymbolName()+"="+this.get(s).toString()+"; ";
		}
		tmp=tmp+"}";
		return tmp;
	} 
	public Set<Symbol> getArrays(){
		return this.keySet();
	}
	public SectionSet getSectionsofArray(Symbol arr){
		return this.get(arr);
	}
	public int get_total_num_of_sections(){
		int n=0;
		for(Symbol s: keySet())
			n+=this.get(s).size();
		return n;
	}
	public int get_total_num_of_section_terms(){
		int n=0;
		for(Symbol s: keySet())
			for(SECTION e: this.get(s))
				if(e.isRSD()) 
					n++;
				else
					n+=((ERSD)e).size();
		return n;
	}
	public boolean containsInfiniteElement(){
		for(Symbol s:this.keySet())
			if(this.get(s).containsInfiniteElement())
				return true;
		return false;
	}
	
	public boolean hasChanged(SectionSet.MAP previous, RangeDomain rd){
		if(previous == null)
			return true;
		if(previous.isEmpty())
			if(this.isEmpty())
				return false;
			else
				return true;
		if(!this.keySet().equals(previous.keySet()))
			return true;
		for(Symbol s: previous.keySet()){
			if(this.get(s).IsEqual(previous.get(s), rd) == false)
				return true;
		}
		return false;
	}
	public boolean hasChanged_xp(SectionSet.MAP previous, RangeDomain rd){
		if(previous == null)
			return true;
		if(previous.isEmpty())
			if(this.isEmpty())
				return false;
			else
				return true;
		if(!this.keySet().equals(previous.keySet()))
			return true;
		for(Symbol s: previous.keySet()){
			if(this.get(s).IsEqual_xp(previous.get(s), rd) == false)
				return true;
		}
		return false;
	}
	public SectionSet.MAP unionWith (SectionSet.MAP other, RangeDomain rd){
		if(other == null || other.isEmpty())
			return  this.clone();
		if(this.isEmpty())
			return  other.clone();
		SectionSet.MAP union = new SectionSet.MAP();
		for(Symbol s: this.keySet())
			if(other.keySet().contains(s))
				union.put(s, this.get(s).unionWith(other.get(s), rd));
		for(Symbol s: this.keySet())
			if(!union.keySet().contains(s))
				union.put(s, (SectionSet)this.get(s).clone());
		for(Symbol s: other.keySet())
			if(!union.keySet().contains(s))
				union.put(s, (SectionSet)other.get(s).clone());
		return union;
	}
	/** this is the union function used with explicit static partitioning method*/
	public SectionSet.MAP unionWith_xp (SectionSet.MAP other, RangeDomain rd){
		if(other == null || other.isEmpty())
			return  this.clone();
		if(this.isEmpty())
			return  other.clone();
		SectionSet.MAP union = new SectionSet.MAP();
		for(Symbol s: this.keySet())
			if(other.keySet().contains(s))
				union.put(s, this.get(s).unionWith_xp(other.get(s), rd));
		for(Symbol s: this.keySet())
			if(!union.keySet().contains(s))
				union.put(s, (SectionSet)this.get(s).clone());
		for(Symbol s: other.keySet())
			if(!union.keySet().contains(s))
				union.put(s, (SectionSet)other.get(s).clone());
		return union;
	}
	
	public boolean IsDisjoint(SectionSet.MAP other, RangeDomain rd){
		if(other == null || other.isEmpty() || this.isEmpty())
			return false;
		for(Symbol s : this.keySet())
			if(other.keySet().contains(s))
				if(this.get(s).IsDisjoint(other.get(s), rd)==false)
					return false;
		return true;
	}
	
	public SectionSet.MAP intersectWith (SectionSet.MAP other, RangeDomain rd){
		if(other == null || other.isEmpty() || this.isEmpty())
			return new SectionSet.MAP();
		SectionSet.MAP intersect = new SectionSet.MAP();
		for(Symbol s : this.keySet()){
			if(other.keySet().contains(s)){
				SectionSet tmp = this.get(s).intersectWith(other.get(s), rd);
				if(tmp.isEmpty()==false)
					intersect.put(s,tmp);
			}
		}
		return intersect;
	}
	
	public SectionSet.MAP subtractFrom (SectionSet.MAP other, RangeDomain rd, boolean enable_delayed_subtraction){
		if( this.isEmpty())
			return new SectionSet.MAP(); 
		if(other == null || other.isEmpty() )
			return this.clone();
		SectionSet.MAP subtract = new SectionSet.MAP();
		for(Symbol s : this.keySet()){
			if(other.keySet().contains(s)){
				SectionSet tmp = this.get(s).subtractFrom(other.get(s), rd, enable_delayed_subtraction);
				if(tmp.isEmpty()==false)
					subtract.put(s,tmp);
			}
			else
				subtract.put(s, this.get(s).clone());
		}
		return subtract;
	}
	
	public SectionSet.MAP subtractFrom_xp (SectionSet.MAP other, RangeDomain rd, boolean enable_delayed_subtraction){
		if( this.isEmpty())
			return new SectionSet.MAP(); 
		if(other == null || other.isEmpty() )
			return this.clone();
		if(enable_delayed_subtraction)
			return subtractFromAccurate_xp(other,rd);
		else
			return subtractFromConservative_xp(other,rd);
	}
	
	public SectionSet.MAP subtractFromAccurate_xp (SectionSet.MAP other, RangeDomain rd){
		SectionSet.MAP subtract = new SectionSet.MAP();
		for(Symbol s : this.keySet()){
			if(other.keySet().contains(s)){
				SectionSet tmp = this.get(s).subtractFrom_xp(other.get(s), rd);
				if(tmp.isEmpty()==false)
					subtract.put(s,tmp);
			}
			else
				subtract.put(s, this.get(s).clone());
		}
		return subtract;
	}
	
	public SectionSet.MAP subtractFromConservative_xp (SectionSet.MAP other, RangeDomain rd){
		SectionSet.MAP subtract = new SectionSet.MAP();
		for(Symbol s : this.keySet()){
			if(other.keySet().contains(s)){
				SectionSet tmp = this.get(s).subtractFromConservative_xp(other.get(s), rd);
				if(tmp.isEmpty()==false)
					subtract.put(s,tmp);
			}
			else
				subtract.put(s, this.get(s).clone());
		}
		return subtract;
	}
	
	public void Serialize(){
		for(Symbol s:this.keySet()){
			this.get(s).Serialize();
		}
	}
	public void Expand(RangeDomain rd, Set<Symbol> Expand){
		if(rd==null)
			return;
		if(rd.getSymbols().isEmpty())
			return;
		for(Symbol s:this.keySet())
			this.get(s).Expand(rd, Expand);
	}
	public void substituteKnowns(RangeDomain rd){
		if(rd==null)
			return;
		if(rd.getSymbols().isEmpty())
			return;
		for(Symbol s:this.keySet())
			this.get(s).substituteKnowns(rd);
	}
	public void substituteKnowns_xp(RangeDomain rd){
		if(rd==null)
			return;
		if(rd.getSymbols().isEmpty())
			return;
		for(Symbol s:this.keySet())
			this.get(s).substituteKnowns_xp(rd);
	}
	public void substitute(Symbol s, Expression expr, RangeDomain rd){
		for(Symbol sml:this.keySet())
			this.get(sml).substitute(s, expr, rd);
	}
	public void RemoveUnknwonSymbols(RangeDomain rd, Set<Symbol> Unknowns){
		if(Unknowns==null || Unknowns.isEmpty())
			return;
		for(Symbol s:this.keySet())
			this.get(s).RemoveUnknwonSymbols(rd, Unknowns);
	}
}

private enum BOOLEAN {TRUE, FALSE, UNKNOWN}

} //end of SectionSet 


