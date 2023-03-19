include "clindf.mm"
include "wbr.mm"
include "wcel.mm"
include "wa.mm"
include "cdm.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "cvsca.mm"
include "co.mm"
include "csn.mm"
include "cdif.mm"
include "cima.mm"
include "clspn.mm"
include "wn.mm"
include "csca.mm"
include "cbs.mm"
include "c0g.mm"
include "wral.mm"
include "simpl.mm"
include "wb.mm"
include "cvv.mm"
include "rellindf.mm"
include "brrelexi.mm"
include "eqid.mm"
include "islindf.mm"
include "sylan2.mm"
include "ancoms.mm"
include "mpbid.mm"
include "simpld.mm"

theorem lindff
  let cB: class B
  let cF: class F
  let cW: class W
  let cY: class Y
  let vk: setvar k
  let vx: setvar x
  assume lindff.b: |- B = ( Base ` W )


  assert |- ( ( F LIndF W /\ W e. Y ) -> F : dom F --> B )

  proof
    cF
    cW
    clindf
    wbr
    #
    cW
    cY
    wcel
    #
    wa
    #
    cF
    cdm
    #
    cB
    cF
    wf
    #
    vk
    cv
    vx
    cv
    #
    cF
    cfv
    cW
    cvsca
    cfv
    #
    co
    cF
    @3
    @5
    csn
    cdif
    cima
    cW
    clspn
    cfv
    #
    cfv
    wcel
    wn
    vk
    cW
    csca
    cfv
    #
    cbs
    cfv
    #
    @8
    c0g
    cfv
    #
    csn
    cdif
    wral
    vx
    @3
    wral
    #
    @2
    @0
    @4
    @11
    wa
    #
    @0
    @1
    simpl
    @1
    @0
    @0
    @12
    wb
    #
    @0
    @1
    cF
    cvv
    wcel
    @13
    cF
    cW
    clindf
    rellindf
    brrelexi
    vx
    cB
    @8
    @6
    vk
    cF
    @7
    @9
    cW
    cvv
    cY
    @10
    lindff.b
    @6
    eqid
    @7
    eqid
    @8
    eqid
    @9
    eqid
    @10
    eqid
    islindf
    sylan2
    ancoms
    mpbid
    simpld
end
