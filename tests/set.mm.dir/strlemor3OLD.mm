include "cop.mm"
include "cpr.mm"
include "cun.mm"
include "eqid.mm"
include "strlemor2OLD.mm"
include "nnnn0i.mm"
include "ctp.mm"
include "csn.mm"
include "df-tp.mm"
include "uneq2i.mm"
include "unass.mm"
include "3eqtr4i.mm"
include "strlemor1OLD.mm"

theorem strlemor3OLD
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G
  let cI: class I
  let cJ: class J
  let cK: class K
  let cL: class L
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume strlemor.f: |- ( Fun `' `' F /\ dom F C_ ( 1 ... I ) )
  assume strlemor.i: |- I e. NN0
  assume strlemor.o: |- I < J
  assume strlemor.j: |- J e. NN
  assume strlemor.a: |- A = J
  assume strlemor2.o: |- J < K
  assume strlemor2.k: |- K e. NN
  assume strlemor2.b: |- B = K
  assume strlemor3.o: |- K < L
  assume strlemor3.l: |- L e. NN
  assume strlemor3.c: |- C = L
  assume strlemor3.g: |- G = ( F u. { <. A , X >. , <. B , Y >. , <. C , Z >. } )


  assert |- ( Fun `' `' G /\ dom G C_ ( 1 ... L ) )

  proof
    cC
    cF
    cA
    cX
    cop
    #
    cB
    cY
    cop
    #
    cpr
    #
    cun
    #
    cG
    cK
    cL
    cZ
    cA
    cB
    cF
    @3
    cI
    cJ
    cK
    cX
    cY
    strlemor.f
    strlemor.i
    strlemor.o
    strlemor.j
    strlemor.a
    strlemor2.o
    strlemor2.k
    strlemor2.b
    @3
    eqid
    strlemor2OLD
    cK
    strlemor2.k
    nnnn0i
    strlemor3.o
    strlemor3.l
    strlemor3.c
    cF
    @0
    @1
    cC
    cZ
    cop
    #
    ctp
    #
    cun
    cF
    @2
    @4
    csn
    #
    cun
    #
    cun
    cG
    @3
    @6
    cun
    @5
    @7
    cF
    @0
    @1
    @4
    df-tp
    uneq2i
    strlemor3.g
    cF
    @2
    @6
    unass
    3eqtr4i
    strlemor1OLD
end
