include "cwwlksn.mm"
include "co.mm"
include "c0.mm"
include "wceq.mm"
include "cvv.mm"
include "wnel.mm"
include "cn0.mm"
include "wo.mm"
include "wn.mm"
include "cv.mm"
include "wcel.mm"
include "wex.mm"
include "neq0.mm"
include "cvtx.mm"
include "cfv.mm"
include "cword.mm"
include "w3a.mm"
include "eqid.mm"
include "wwlknbp.mm"
include "wa.mm"
include "nnel.mm"
include "anbi12i.mm"
include "biimpri.mm"
include "3adant3.mm"
include "ioran.mm"
include "sylibr.mm"
include "syl.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "con4i.mm"

theorem wwlksnndef
  let cG: class G
  let cN: class N
  let vw: setvar w


  assert |- ( ( G e/ _V \/ N e/ NN0 ) -> ( N WWalksN G ) = (/) )

  proof
    cN
    cG
    cwwlksn
    co
    #
    c0
    wceq
    #
    cG
    cvv
    wnel
    #
    cN
    cn0
    wnel
    #
    wo
    #
    @1
    wn
    vw
    cv
    #
    @0
    wcel
    #
    vw
    wex
    @4
    wn
    #
    vw
    @0
    neq0
    @6
    @7
    vw
    @6
    cG
    cvv
    wcel
    #
    cN
    cn0
    wcel
    #
    @5
    cG
    cvtx
    cfv
    #
    cword
    wcel
    #
    w3a
    #
    @7
    cG
    cN
    @10
    @5
    @10
    eqid
    wwlknbp
    @12
    @2
    wn
    #
    @3
    wn
    #
    wa
    #
    @7
    @8
    @9
    @15
    @11
    @15
    @8
    @9
    wa
    @13
    @8
    @14
    @9
    cG
    cvv
    nnel
    cN
    cn0
    nnel
    anbi12i
    biimpri
    3adant3
    @2
    @3
    ioran
    sylibr
    syl
    exlimiv
    sylbi
    con4i
end
