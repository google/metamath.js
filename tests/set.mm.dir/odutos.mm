include "ctos.mm"
include "wcel.mm"
include "cpo.mm"
include "cv.mm"
include "cple.mm"
include "cfv.mm"
include "ccnv.mm"
include "wbr.mm"
include "wo.mm"
include "cbs.mm"
include "wral.mm"
include "tospos.mm"
include "odupos.mm"
include "syl.mm"
include "w3a.mm"
include "eqid.mm"
include "tleile.mm"
include "vex.mm"
include "brcnv.mm"
include "orbi12i.mm"
include "sylibr.mm"
include "3com23.mm"
include "3expb.mm"
include "ralrimivva.mm"
include "odubas.mm"
include "oduleval.mm"
include "istos.mm"
include "sylanbrc.mm"

theorem odutos
  let cD: class D
  let cK: class K
  let vx: setvar x
  let vy: setvar y
  assume odutos.d: |- D = ( ODual ` K )


  assert |- ( K e. Toset -> D e. Toset )

  proof
    cK
    ctos
    wcel
    #
    cD
    cpo
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cK
    cple
    cfv
    #
    ccnv
    #
    wbr
    #
    @3
    @2
    @5
    wbr
    #
    wo
    #
    vy
    cK
    cbs
    cfv
    #
    wral
    vx
    @9
    wral
    cD
    ctos
    wcel
    @0
    cK
    cpo
    wcel
    @1
    cK
    tospos
    cD
    cK
    odutos.d
    odupos
    syl
    @0
    @8
    vx
    vy
    @9
    @9
    @0
    @2
    @9
    wcel
    #
    @3
    @9
    wcel
    #
    @8
    @0
    @11
    @10
    @8
    @0
    @11
    @10
    w3a
    @3
    @2
    @4
    wbr
    #
    @2
    @3
    @4
    wbr
    #
    wo
    @8
    @9
    cK
    @4
    @3
    @2
    @9
    eqid
    #
    @4
    eqid
    #
    tleile
    @6
    @12
    @7
    @13
    @2
    @3
    @4
    vx
    vex
    #
    vy
    vex
    #
    brcnv
    @3
    @2
    @4
    @17
    @16
    brcnv
    orbi12i
    sylibr
    3com23
    3expb
    ralrimivva
    vx
    vy
    @9
    cD
    @5
    @9
    cD
    cK
    odutos.d
    @14
    odubas
    cD
    @4
    cK
    odutos.d
    @15
    oduleval
    istos
    sylanbrc
end
