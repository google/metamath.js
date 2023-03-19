include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wne.mm"
include "wa.mm"
include "c0.mm"
include "cbs.mm"
include "cfv.mm"
include "wcel.mm"
include "citv.mm"
include "eqid.mm"
include "cstrkg.mm"
include "ad3antrrr.mm"
include "simpllr.mm"
include "simplr.mm"
include "simprr.mm"
include "tglinerflx1.mm"
include "simprl.mm"
include "eleqtrrd.mm"
include "ne0i.mm"
include "syl.mm"
include "tgisline.mm"
include "r19.29vva.mm"

theorem tglnne0
  let wph: wff ph
  let cA: class A
  let cG: class G
  let cL: class L
  let vx: setvar x
  let vy: setvar y
  assume tglnne0.l: |- L = ( LineG ` G )
  assume tglnne0.g: |- ( ph -> G e. TarskiG )
  assume tglnne0.1: |- ( ph -> A e. ran L )


  assert |- ( ph -> A =/= (/) )

  proof
    wph
    cA
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
    @0
    @1
    wne
    #
    wa
    #
    cA
    c0
    wne
    #
    vx
    vy
    cG
    cbs
    cfv
    #
    @7
    wph
    @0
    @7
    wcel
    #
    wa
    #
    @1
    @7
    wcel
    #
    wa
    #
    @5
    wa
    #
    @0
    cA
    wcel
    @6
    @12
    @0
    @2
    cA
    @12
    @7
    @0
    @1
    cG
    cG
    citv
    cfv
    #
    cL
    @7
    eqid
    #
    @13
    eqid
    #
    tglnne0.l
    wph
    cG
    cstrkg
    wcel
    @8
    @10
    @5
    tglnne0.g
    ad3antrrr
    wph
    @8
    @10
    @5
    simpllr
    @9
    @10
    @5
    simplr
    @11
    @3
    @4
    simprr
    tglinerflx1
    @11
    @3
    @4
    simprl
    eleqtrrd
    cA
    @0
    ne0i
    syl
    wph
    vx
    vy
    cA
    @7
    cG
    @13
    cL
    @14
    @15
    tglnne0.l
    tglnne0.g
    tglnne0.1
    tgisline
    r19.29vva
end
