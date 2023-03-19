include "cop.mm"
include "csn.mm"
include "cun.mm"
include "eqid.mm"
include "strlemor1OLD.mm"
include "nnnn0i.mm"
include "cpr.mm"
include "df-pr.mm"
include "uneq2i.mm"
include "unass.mm"
include "3eqtr4i.mm"

theorem strlemor2OLD
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cI: class I
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  assume strlemor.f: |- ( Fun `' `' F /\ dom F C_ ( 1 ... I ) )
  assume strlemor.i: |- I e. NN0
  assume strlemor.o: |- I < J
  assume strlemor.j: |- J e. NN
  assume strlemor.a: |- A = J
  assume strlemor2.o: |- J < K
  assume strlemor2.k: |- K e. NN
  assume strlemor2.b: |- B = K
  assume strlemor2.g: |- G = ( F u. { <. A , X >. , <. B , Y >. } )


  assert |- ( Fun `' `' G /\ dom G C_ ( 1 ... K ) )

  proof
    cB
    cF
    cA
    cX
    cop
    #
    csn
    #
    cun
    #
    cG
    cJ
    cK
    cY
    cA
    cF
    @2
    cI
    cJ
    cX
    strlemor.f
    strlemor.i
    strlemor.o
    strlemor.j
    strlemor.a
    @2
    eqid
    strlemor1OLD
    cJ
    strlemor.j
    nnnn0i
    strlemor2.o
    strlemor2.k
    strlemor2.b
    cF
    @0
    cB
    cY
    cop
    #
    cpr
    #
    cun
    cF
    @1
    @3
    csn
    #
    cun
    #
    cun
    cG
    @2
    @5
    cun
    @4
    @6
    cF
    @0
    @3
    df-pr
    uneq2i
    strlemor2.g
    cF
    @1
    @5
    unass
    3eqtr4i
    strlemor1OLD
end
