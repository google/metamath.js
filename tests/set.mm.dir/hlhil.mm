include "chl.mm"
include "wcel.mm"
include "cphl.mm"
include "cpj.mm"
include "cfv.mm"
include "cdm.mm"
include "ccss.mm"
include "wceq.mm"
include "chs.mm"
include "hlphl.mm"
include "wss.mm"
include "eqid.mm"
include "pjcss.mm"
include "syl.mm"
include "clss.mm"
include "ctopn.mm"
include "ccld.mm"
include "cin.mm"
include "cbs.mm"
include "cldcss2.mm"
include "cv.mm"
include "wa.mm"
include "elin.mm"
include "pjth2.mm"
include "3expib.mm"
include "syl5bi.mm"
include "ssrdv.mm"
include "eqsstrd.mm"
include "eqssd.mm"
include "ishil.mm"
include "sylanbrc.mm"

theorem hlhil
  let cW: class W
  let vx: setvar x


  assert |- ( W e. CHil -> W e. Hil )

  proof
    cW
    chl
    wcel
    #
    cW
    cphl
    wcel
    #
    cW
    cpj
    cfv
    #
    cdm
    #
    cW
    ccss
    cfv
    #
    wceq
    cW
    chs
    wcel
    cW
    hlphl
    #
    @0
    @3
    @4
    @0
    @1
    @3
    @4
    wss
    @5
    @4
    @2
    cW
    @2
    eqid
    #
    @4
    eqid
    #
    pjcss
    syl
    @0
    @4
    cW
    clss
    cfv
    #
    cW
    ctopn
    cfv
    #
    ccld
    cfv
    #
    cin
    #
    @3
    @4
    @9
    @8
    cW
    cbs
    cfv
    #
    cW
    @12
    eqid
    @9
    eqid
    #
    @8
    eqid
    #
    @7
    cldcss2
    @0
    vx
    @11
    @3
    vx
    cv
    #
    @11
    wcel
    @15
    @8
    wcel
    #
    @15
    @10
    wcel
    #
    wa
    @0
    @15
    @3
    wcel
    #
    @15
    @8
    @10
    elin
    @0
    @16
    @17
    @18
    @15
    @9
    @2
    @8
    cW
    @13
    @14
    @6
    pjth2
    3expib
    syl5bi
    ssrdv
    eqsstrd
    eqssd
    @4
    cW
    @2
    @6
    @7
    ishil
    sylanbrc
end
