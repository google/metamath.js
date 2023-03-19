include "ctb.mm"
include "wcel.mm"
include "ctg.mm"
include "cfv.mm"
include "ctop.mm"
include "tgcl.mm"
include "cv.mm"
include "cin.mm"
include "wss.mm"
include "wa.mm"
include "wrex.mm"
include "wral.mm"
include "cvv.mm"
include "c0.mm"
include "0opn.mm"
include "elfvexd.mm"
include "bastg.mm"
include "syl.mm"
include "sselda.mm"
include "anim12dan.mm"
include "inopn.mm"
include "3expb.mm"
include "syldan.mm"
include "tg2.mm"
include "ralrimiva.mm"
include "ralrimivva.mm"
include "wb.mm"
include "isbasis2g.mm"
include "mpbird.mm"
include "impbii.mm"

theorem tgclb
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cJ: class J
  let cV: class V
  let cC: class C


  assert |- ( B e. TopBases <-> ( topGen ` B ) e. Top )

  proof
    cB
    ctb
    wcel
    #
    cB
    ctg
    cfv
    #
    ctop
    wcel
    #
    cB
    tgcl
    @2
    @0
    vz
    cv
    #
    vw
    cv
    #
    wcel
    @4
    vx
    cv
    #
    vy
    cv
    #
    cin
    #
    wss
    wa
    vw
    cB
    wrex
    #
    vz
    @7
    wral
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    @2
    @9
    vx
    vy
    cB
    cB
    @2
    @5
    cB
    wcel
    #
    @6
    cB
    wcel
    #
    wa
    #
    wa
    @7
    @1
    wcel
    #
    @9
    @2
    @13
    @5
    @1
    wcel
    #
    @6
    @1
    wcel
    #
    wa
    @14
    @2
    @11
    @15
    @12
    @16
    @2
    cB
    @1
    @5
    @2
    cB
    cvv
    wcel
    #
    cB
    @1
    wss
    @2
    c0
    ctg
    cB
    @1
    0opn
    elfvexd
    #
    cB
    cvv
    bastg
    syl
    #
    sselda
    @2
    cB
    @1
    @6
    @19
    sselda
    anim12dan
    @2
    @15
    @16
    @14
    @5
    @6
    @1
    inopn
    3expb
    syldan
    @14
    @8
    vz
    @7
    vw
    @7
    cB
    @3
    tg2
    ralrimiva
    syl
    ralrimivva
    @2
    @17
    @0
    @10
    wb
    @18
    vx
    vy
    vz
    vw
    cB
    cvv
    isbasis2g
    syl
    mpbird
    impbii
end
