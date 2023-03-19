include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cind.mm"
include "cfv.mm"
include "c1.mm"
include "cc0.mm"
include "cif.mm"
include "wceq.mm"
include "simp2.mm"
include "simp3.mm"
include "sseldd.mm"
include "indfval.mm"
include "syld3an3.mm"
include "iftrue.mm"
include "3ad2ant3.mm"
include "eqtrd.mm"

theorem ind1
  let cA: class A
  let cO: class O
  let cV: class V
  let cX: class X


  assert |- ( ( O e. V /\ A C_ O /\ X e. A ) -> ( ( ( _Ind ` O ) ` A ) ` X ) = 1 )

  proof
    cO
    cV
    wcel
    #
    cA
    cO
    wss
    #
    cX
    cA
    wcel
    #
    w3a
    #
    cX
    cA
    cO
    cind
    cfv
    cfv
    cfv
    #
    @2
    c1
    cc0
    cif
    #
    c1
    @0
    @1
    @2
    cX
    cO
    wcel
    @4
    @5
    wceq
    @3
    cA
    cO
    cX
    @0
    @1
    @2
    simp2
    @0
    @1
    @2
    simp3
    sseldd
    cA
    cO
    cV
    cX
    indfval
    syld3an3
    @2
    @0
    @5
    c1
    wceq
    @1
    @2
    c1
    cc0
    iftrue
    3ad2ant3
    eqtrd
end
