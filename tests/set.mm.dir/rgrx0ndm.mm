include "cc0.mm"
include "cdm.mm"
include "wnel.mm"
include "cxnn0.mm"
include "wcel.mm"
include "cv.mm"
include "cvtxdg.mm"
include "cfv.mm"
include "wceq.mm"
include "cvtx.mm"
include "wral.mm"
include "cab.mm"
include "cvv.mm"
include "wa.mm"
include "wn.mm"
include "rgrprcx.mm"
include "neli.mm"
include "intnan.mm"
include "df-nel.mm"
include "crab.mm"
include "dmmpt.mm"
include "eleq2i.mm"
include "eqeq2.mm"
include "ralbidv.mm"
include "abbidv.mm"
include "eleq1d.mm"
include "elrab.mm"
include "bitri.mm"
include "xchbinx.mm"
include "mpbir.mm"

theorem rgrx0ndm
  let vv: setvar v
  let cR: class R
  let vg: setvar g
  let vk: setvar k
  assume rgrx0ndm.u: |- R = ( k e. NN0* |-> { g | A. v e. ( Vtx ` g ) ( ( VtxDeg ` g ) ` v ) = k } )

  disjoint g k
  disjoint g v
  disjoint k v
  assert |- 0 e/ dom R

  proof
    cc0
    cR
    cdm
    #
    wnel
    #
    cc0
    cxnn0
    wcel
    #
    vv
    cv
    vg
    cv
    #
    cvtxdg
    cfv
    cfv
    #
    cc0
    wceq
    #
    vv
    @3
    cvtx
    cfv
    #
    wral
    #
    vg
    cab
    #
    cvv
    wcel
    #
    wa
    #
    wn
    @9
    @2
    @8
    cvv
    vv
    vg
    rgrprcx
    neli
    intnan
    @1
    cc0
    @0
    wcel
    #
    @10
    cc0
    @0
    df-nel
    @11
    cc0
    @4
    vk
    cv
    #
    wceq
    #
    vv
    @6
    wral
    #
    vg
    cab
    #
    cvv
    wcel
    #
    vk
    cxnn0
    crab
    #
    wcel
    @10
    @0
    @17
    cc0
    vk
    cxnn0
    @15
    cR
    rgrx0ndm.u
    dmmpt
    eleq2i
    @16
    @9
    vk
    cc0
    cxnn0
    @12
    cc0
    wceq
    #
    @15
    @8
    cvv
    @18
    @14
    @7
    vg
    @18
    @13
    @5
    vv
    @6
    @12
    cc0
    @4
    eqeq2
    ralbidv
    abbidv
    eleq1d
    elrab
    bitri
    xchbinx
    mpbir
end
