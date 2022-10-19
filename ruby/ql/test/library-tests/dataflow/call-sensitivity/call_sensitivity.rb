def taint x
    x
end

def sink x
    puts "SINK: #{x}"
end

sink (taint 1) # $ hasValueFlow=1

def yielder x
    yield x
end

yielder ("no taint") { |x| sink x }

yielder (taint 2) { |x| puts x }

yielder (taint 3) { |x| sink x } # $ hasValueFlow=3

def apply_lambda (lambda, x)
    lambda.call(x)
end

my_lambda = -> (x) { sink x }
apply_lambda(my_lambda, "no taint")

my_lambda = -> (x) { puts x }
apply_lambda(my_lambda, taint(4))

my_lambda = -> (x) { sink x } # $ hasValueFlow=5
apply_lambda(my_lambda, taint(5))

my_lambda = lambda { |x| sink x }
apply_lambda(my_lambda, "no taint")

my_lambda = lambda { |x| puts x }
apply_lambda(my_lambda, taint(6))

my_lambda = lambda { |x| sink x } # $ hasValueFlow=7
apply_lambda(my_lambda, taint(7))

MY_LAMBDA1 = lambda { |x| sink x } # $ hasValueFlow=8
apply_lambda(MY_LAMBDA1, taint(8))

MY_LAMBDA2 = lambda { |x| puts x }
apply_lambda(MY_LAMBDA2, taint(9))

class A
  def method1 x
    sink x # $ hasValueFlow=10 $ hasValueFlow=11 $ hasValueFlow=12 $ hasValueFlow=13
  end

  def method2 x
    method1 x
  end

  def call_method2 x
    self.method2 x
  end

  def method3(x, y)
    x.method1(y)
  end

  def call_method3 x
    self.method3(self, x)
  end

  def self.singleton_method1 x
    sink x # $ hasValueFlow=14 $ hasValueFlow=15 # $ hasValueFlow=16 $ hasValueFlow=17
  end

  def self.singleton_method2 x
    singleton_method1 x
  end

  def self.call_singleton_method2 x
    self.singleton_method2 x
  end

  def self.singleton_method3(x, y)
    x.singleton_method1(y)
  end

  def self.call_singleton_method3 x
    self.singleton_method3(self, x)
  end
end

a = A.new
a.method2(taint 10)
a.call_method2(taint 11)
a.method3(a, taint(12))
a.call_method3(taint(13))

A.singleton_method2(taint 14)
A.call_singleton_method2(taint 15)
A.singleton_method3(A, taint(16))
A.call_singleton_method3(taint 17)

class B < A
  def method1 x
    puts "NON SINK: #{x}"
  end

  def self.singleton_method1 x
    puts "NON SINK: #{x}"
  end

  def call_method2 x
    self.method2 x
  end

  def call_method3 x
    self.method3(self, x)
  end

  def self.call_singleton_method2 x
    self.singleton_method2 x
  end

  def self.call_singleton_method3 x
    self.singleton_method3(self, x)
  end
end

b = B.new
b.method2(taint 18)
b.call_method2(taint 19)
b.method3(b, taint(20))
b.call_method3(taint(21))

B.singleton_method2(taint 22)
B.call_singleton_method2(taint 23)
B.singleton_method3(B, taint(24))
B.call_singleton_method3(taint 25)
