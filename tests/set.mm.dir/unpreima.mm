include "wfun.mm"
include "cdm.mm"
include "wfn.mm"
include "ccnv.mm"
include "cun.mm"
include "cima.mm"
include "wceq.mm"
include "funfn.mm"
include "cv.mm"
include "wcel.mm"
include "cfv.mm"
include "wa.mm"
include "elpreima.mm"
include "wo.mm"
include "elun.mm"
include "orbi12d.mm"
include "syl5bb.mm"
include "anbi2i.mm"
include "andi.mm"
include "bitri.mm"
include "syl6rbbr.mm"
include "bitrd.mm"
include "eqrdv.mm"
include "sylbi.mm"

theorem unpreima
  let cA: class A
  let cB: class B
  let cF: class F
  let vx: setvar x


  assert |- ( Fun F -> ( `' F " ( A u. B ) ) = ( ( `' F " A ) u. ( `' F " B ) ) )

  proof
    cF
    wfun
    cF
    cF
    cdm
    #
    wfn
    #
    cF
    ccnv
    #
    cA
    cB
    cun
    #
    cima
    #
    @2
    cA
    cima
    #
    @2
    cB
    cima
    #
    cun
    #
    wceq
    cF
    funfn
    @1
    vx
    @4
    @7
    @1
    vx
    cv
    #
    @4
    wcel
    @8
    @0
    wcel
    #
    @8
    cF
    cfv
    #
    @3
    wcel
    #
    wa
    #
    @8
    @7
    wcel
    #
    @0
    @8
    @3
    cF
    elpreima
    @1
    @13
    @9
    @10
    cA
    wcel
    #
    wa
    #
    @9
    @10
    cB
    wcel
    #
    wa
    #
    wo
    #
    @12
    @13
    @8
    @5
    wcel
    #
    @8
    @6
    wcel
    #
    wo
    @1
    @18
    @8
    @5
    @6
    elun
    @1
    @19
    @15
    @20
    @17
    @0
    @8
    cA
    cF
    elpreima
    @0
    @8
    cB
    cF
    elpreima
    orbi12d
    syl5bb
    @12
    @9
    @14
    @16
    wo
    #
    wa
    @18
    @11
    @21
    @9
    @10
    cA
    cB
    elun
    anbi2i
    @9
    @14
    @16
    andi
    bitri
    syl6rbbr
    bitrd
    eqrdv
    sylbi
end
