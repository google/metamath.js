include "cop.mm"
include "cpr.mm"
include "csn.mm"
include "cun.mm"
include "cstr.mm"
include "df-pr.mm"
include "strle1.mm"
include "strleun.mm"
include "eqbrtri.mm"

theorem strle2
  let cA: class A
  let cB: class B
  let cI: class I
  let cJ: class J
  let cX: class X
  let cY: class Y
  assume strle1.i: |- I e. NN
  assume strle1.a: |- A = I
  assume strle2.j: |- I < J
  assume strle2.k: |- J e. NN
  assume strle2.b: |- B = J


  assert |- { <. A , X >. , <. B , Y >. } Struct <. I , J >.

  proof
    cA
    cX
    cop
    #
    cB
    cY
    cop
    #
    cpr
    @0
    csn
    #
    @1
    csn
    #
    cun
    cI
    cJ
    cop
    cstr
    @0
    @1
    df-pr
    cI
    cI
    cJ
    cJ
    @2
    @3
    cA
    cI
    cX
    strle1.i
    strle1.a
    strle1
    cB
    cJ
    cY
    strle2.k
    strle2.b
    strle1
    strle2.j
    strleun
    eqbrtri
end
