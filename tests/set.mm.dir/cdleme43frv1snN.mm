include "cdleme31sn2.mm"

theorem cdleme43frv1snN
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cU: class U
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cW: class W
  let cX: class X
  let vs: setvar s
  let vz: setvar z
  let vx: setvar x
  assume cdlemefr27.b: |- B = ( Base ` K )
  assume cdlemefr27.l: |- .<_ = ( le ` K )
  assume cdlemefr27.j: |- .\/ = ( join ` K )
  assume cdlemefr27.m: |- ./\ = ( meet ` K )
  assume cdlemefr27.a: |- A = ( Atoms ` K )
  assume cdlemefr27.h: |- H = ( LHyp ` K )
  assume cdlemefr27.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdlemefr27.c: |- C = ( ( s .\/ U ) ./\ ( Q .\/ ( ( P .\/ s ) ./\ W ) ) )
  assume cdlemefr27.n: |- N = if ( s .<_ ( P .\/ Q ) , I , C )
  assume cdleme43fr.x: |- X = ( ( R .\/ U ) ./\ ( Q .\/ ( ( P .\/ R ) ./\ W ) ) )

  disjoint A s
  disjoint .\/ s
  disjoint .<_ s
  disjoint ./\ s
  disjoint P s
  disjoint Q s
  disjoint R s
  disjoint U s
  disjoint W s
  disjoint H s
  disjoint K s
  disjoint B s
  disjoint s z
  disjoint x z
  disjoint A x
  disjoint A z
  disjoint s x
  disjoint B x
  disjoint B z
  disjoint H z
  disjoint .\/ x
  disjoint .\/ z
  disjoint K z
  disjoint .<_ x
  disjoint .<_ z
  disjoint ./\ x
  disjoint ./\ z
  disjoint N x
  disjoint N z
  disjoint P z
  disjoint Q z
  disjoint R x
  disjoint R z
  disjoint W x
  disjoint W z
  assert |- ( ( R e. A /\ -. R .<_ ( P .\/ Q ) ) -> [_ R / s ]_ N = X )

  proof
    cA
    cX
    cC
    cP
    cQ
    cR
    cU
    cI
    c.or
    c.le
    c.an
    cN
    cW
    vs
    cdlemefr27.c
    cdlemefr27.n
    cdleme43fr.x
    cdleme31sn2
end
