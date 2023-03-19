include "ccmp.mm"
include "wcel.mm"
include "ccld.mm"
include "cfv.mm"
include "wss.mm"
include "c0.mm"
include "cfi.mm"
include "wn.mm"
include "cint.mm"
include "wne.mm"
include "cpw.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "fvex.mm"
include "elpw2.mm"
include "biimpri.mm"
include "ctop.mm"
include "wb.mm"
include "cmptop.mm"
include "cmpfi.mm"
include "syl.mm"
include "ibi.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "notbid.mm"
include "inteq.mm"
include "neeq1d.mm"
include "imbi12d.mm"
include "rspcva.mm"
include "syl2anr.mm"
include "3impia.mm"

theorem cmpfii
  let cJ: class J
  let cX: class X
  let vx: setvar x


  assert |- ( ( J e. Comp /\ X C_ ( Clsd ` J ) /\ -. (/) e. ( fi ` X ) ) -> |^| X =/= (/) )

  proof
    cJ
    ccmp
    wcel
    #
    cX
    cJ
    ccld
    cfv
    #
    wss
    #
    c0
    cX
    cfi
    cfv
    #
    wcel
    #
    wn
    #
    cX
    cint
    #
    c0
    wne
    #
    @2
    cX
    @1
    cpw
    #
    wcel
    #
    c0
    vx
    cv
    #
    cfi
    cfv
    #
    wcel
    #
    wn
    #
    @10
    cint
    #
    c0
    wne
    #
    wi
    #
    vx
    @8
    wral
    #
    @5
    @7
    wi
    #
    @0
    @9
    @2
    cX
    @1
    cJ
    ccld
    fvex
    elpw2
    biimpri
    @0
    @17
    @0
    cJ
    ctop
    wcel
    @0
    @17
    wb
    cJ
    cmptop
    vx
    cJ
    cmpfi
    syl
    ibi
    @16
    @18
    vx
    cX
    @8
    @10
    cX
    wceq
    #
    @13
    @5
    @15
    @7
    @19
    @12
    @4
    @19
    @11
    @3
    c0
    @10
    cX
    cfi
    fveq2
    eleq2d
    notbid
    @19
    @14
    @6
    c0
    @10
    cX
    inteq
    neeq1d
    imbi12d
    rspcva
    syl2anr
    3impia
end
