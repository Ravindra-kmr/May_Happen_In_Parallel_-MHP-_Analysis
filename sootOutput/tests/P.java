class P{
	public static void main(String []args){
			B t1;
			C t2;
			Buf b;
		try {
			t1 = new B();
			t2 = new C();
			b = new Buf();
			t1.b = b;
			t2.b = b;

			t1.start();
			t2.start();
			t1.join();
			t2.join();
		} catch (Exception e){}
	}	
}
class Buf{
}
class B extends Thread {
	Buf b;
	public void run() {
	try {
		this.bar();
		synchronized (b){
			this.car();
			b.wait();
			this.foo();
		}
	
	} catch (Exception e){}
	}
	public void foo(){ } 
	public void bar(){ } 
	public void car(){ }
}

class C extends Thread {
	Buf b;
	public void run() {
	try {
		this.f2();
		synchronized (b) {
			b.notifyAll();
			this.f3();
		}

	} catch (Exception e){}
	}
	public void f2(){}
	public void f3(){}
}