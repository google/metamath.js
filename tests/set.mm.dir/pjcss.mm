include "cphl.mm"
include "wcel.mm"
include "cdm.mm"
include "cv.mm"
include "wa.mm"
include "clsm.mm"
include "cfv.mm"
include "cocv.mm"
include "cbs.mm"
include "eqid.mm"
include "simpl.mm"
include "clss.mm"
include "wss.mm"
include "co.mm"
include "wceq.mm"
include "pjdm2.mm"
include "simprbda.mm"
include "lssss.mm"
include "syl.mm"
include "ocvss.mm"
include "simplbda.mm"
include "syl5sseqr.mm"
include "lsmcss.mm"
include "ex.mm"
include "ssrdv.mm"

theorem pjcss
  let cC: class C
  let cK: class K
  let cW: class W
  let vx: setvar x
  assume pjcss.k: |- K = ( proj ` W )
  assume pjcss.c: |- C = ( CSubSp ` W )


  assert |- ( W e. PreHil -> dom K C_ C )

  proof
    cW
    cphl
    wcel
    #
    vx
    cK
    cdm
    #
    cC
    @0
    vx
    cv
    #
    @1
    wcel
    #
    @2
    cC
    wcel
    @0
    @3
    wa
    #
    cC
    cW
    clsm
    cfv
    #
    @2
    cW
    cocv
    cfv
    #
    cW
    cbs
    cfv
    #
    cW
    pjcss.c
    @7
    eqid
    #
    @6
    eqid
    #
    @5
    eqid
    #
    @0
    @3
    simpl
    @4
    @2
    cW
    clss
    cfv
    #
    wcel
    #
    @2
    @7
    wss
    @0
    @3
    @12
    @2
    @2
    @6
    cfv
    #
    @5
    co
    #
    @7
    wceq
    #
    @5
    @2
    cK
    @11
    @6
    @7
    cW
    @8
    @11
    eqid
    #
    @9
    @10
    pjcss.k
    pjdm2
    #
    simprbda
    @11
    @2
    @7
    cW
    @8
    @16
    lssss
    syl
    @4
    @7
    @13
    @6
    cfv
    @14
    @13
    @6
    @7
    cW
    @8
    @9
    ocvss
    @0
    @3
    @12
    @15
    @17
    simplbda
    syl5sseqr
    lsmcss
    ex
    ssrdv
end
