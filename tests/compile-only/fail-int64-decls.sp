int64 G;
native int64 q();
void f(int64& x) {
}

methodmap X {
  property int64 Blah {
    public get() { }
  }
};

public main()
{
  int g;
  int64 a[100];
  int64[] b = new int64[g];
  static int64 c;
  f(c);
  f(G);
  f(view_as<int64>(g));
}
