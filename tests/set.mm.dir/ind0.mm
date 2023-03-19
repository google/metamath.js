include "wcel.mm"
include "wss.mm"
include "cdif.mm"
include "w3a.mm"
include "cind.mm"
include "cfv.mm"
include "c1.mm"
include "cc0.mm"
include "cif.mm"
include "wceq.mm"
include "eldifi.mm"
include "indfval.mm"
include "syl3an3.mm"
include "wn.mm"
include "eldifn.mm"
include "3ad2ant3.mm"
include "iffalsed.mm"
include "eqtrd.mm"

theorem ind0
  let cA: class A
  let cO: class O
  let cV: class V
  let cX: class X


  assert |- ( ( O e. V /\ A C_ O /\ X e. ( O \ A ) ) -> ( ( ( _Ind ` O ) ` A ) ` X ) = 0 )

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
    cO
    cA
    cdif
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
    cX
    cA
    wcel
    #
    c1
    cc0
    cif
    #
    cc0
    @2
    @0
    @1
    cX
    cO
    wcel
    @4
    @6
    wceq
    cX
    cO
    cA
    eldifi
    cA
    cO
    cV
    cX
    indfval
    syl3an3
    @3
    @5
    c1
    cc0
    @2
    @0
    @5
    wn
    @1
    cX
    cO
    cA
    eldifn
    3ad2ant3
    iffalsed
    eqtrd
end
