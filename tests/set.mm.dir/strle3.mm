include "cop.mm"
include "ctp.mm"
include "cpr.mm"
include "csn.mm"
include "cun.mm"
include "cstr.mm"
include "df-tp.mm"
include "strle2.mm"
include "strle1.mm"
include "strleun.mm"
include "eqbrtri.mm"

theorem strle3
  let cA: class A
  let cB: class B
  let cC: class C
  let cI: class I
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume strle1.i: |- I e. NN
  assume strle1.a: |- A = I
  assume strle2.j: |- I < J
  assume strle2.k: |- J e. NN
  assume strle2.b: |- B = J
  assume strle3.k: |- J < K
  assume strle3.l: |- K e. NN
  assume strle3.c: |- C = K


  assert |- { <. A , X >. , <. B , Y >. , <. C , Z >. } Struct <. I , K >.

  proof
    cA
    cX
    cop
    #
    cB
    cY
    cop
    #
    cC
    cZ
    cop
    #
    ctp
    @0
    @1
    cpr
    #
    @2
    csn
    #
    cun
    cI
    cK
    cop
    cstr
    @0
    @1
    @2
    df-tp
    cI
    cJ
    cK
    cK
    @3
    @4
    cA
    cB
    cI
    cJ
    cX
    cY
    strle1.i
    strle1.a
    strle2.j
    strle2.k
    strle2.b
    strle2
    cC
    cK
    cZ
    strle3.l
    strle3.c
    strle1
    strle3.k
    strleun
    eqbrtri
end
