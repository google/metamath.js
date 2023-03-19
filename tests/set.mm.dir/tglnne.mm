include "co.mm"
include "cv.mm"
include "wceq.mm"
include "wne.mm"
include "wa.mm"
include "wcel.mm"
include "cstrkg.mm"
include "ad3antrrr.mm"
include "simpllr.mm"
include "simplr.mm"
include "simprr.mm"
include "cds.mm"
include "cfv.mm"
include "eqid.mm"
include "tgbtwntriv1.mm"
include "btwnlng1.mm"
include "simprl.mm"
include "eleqtrrd.mm"
include "tglngne.mm"
include "tgisline.mm"
include "r19.29vva.mm"

theorem tglnne
  let wph: wff ph
  let cB: class B
  let cG: class G
  let cI: class I
  let cL: class L
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume tglineelsb2.p: |- B = ( Base ` G )
  assume tglineelsb2.i: |- I = ( Itv ` G )
  assume tglineelsb2.l: |- L = ( LineG ` G )
  assume tglineelsb2.g: |- ( ph -> G e. TarskiG )
  assume tglnne.x: |- ( ph -> X e. B )
  assume tglnne.y: |- ( ph -> Y e. B )
  assume tglnne.1: |- ( ph -> ( X L Y ) e. ran L )


  assert |- ( ph -> X =/= Y )

  proof
    wph
    cX
    cY
    cL
    co
    #
    vx
    cv
    #
    vy
    cv
    #
    cL
    co
    #
    wceq
    #
    @1
    @2
    wne
    #
    wa
    #
    cX
    cY
    wne
    vx
    vy
    cB
    cB
    wph
    @1
    cB
    wcel
    #
    wa
    #
    @2
    cB
    wcel
    #
    wa
    #
    @6
    wa
    #
    cB
    cG
    cI
    cL
    cX
    cY
    @1
    tglineelsb2.p
    tglineelsb2.l
    tglineelsb2.i
    wph
    cG
    cstrkg
    wcel
    @7
    @9
    @6
    tglineelsb2.g
    ad3antrrr
    #
    wph
    cX
    cB
    wcel
    @7
    @9
    @6
    tglnne.x
    ad3antrrr
    wph
    cY
    cB
    wcel
    @7
    @9
    @6
    tglnne.y
    ad3antrrr
    @11
    @1
    @3
    @0
    @11
    cB
    cG
    cI
    cL
    @1
    @2
    @1
    tglineelsb2.p
    tglineelsb2.i
    tglineelsb2.l
    @12
    wph
    @7
    @9
    @6
    simpllr
    #
    @8
    @9
    @6
    simplr
    #
    @13
    @10
    @4
    @5
    simprr
    @11
    @1
    @2
    cB
    cG
    cI
    cG
    cds
    cfv
    #
    tglineelsb2.p
    @15
    eqid
    tglineelsb2.i
    @12
    @13
    @14
    tgbtwntriv1
    btwnlng1
    @10
    @4
    @5
    simprl
    eleqtrrd
    tglngne
    wph
    vx
    vy
    @0
    cB
    cG
    cI
    cL
    tglineelsb2.p
    tglineelsb2.i
    tglineelsb2.l
    tglineelsb2.g
    tglnne.1
    tgisline
    r19.29vva
end
