include "ctop.mm"
include "wcel.mm"
include "ckq.mm"
include "cfv.mm"
include "cuni.mm"
include "cv.mm"
include "crab.mm"
include "cmpt.mm"
include "crn.mm"
include "ctopon.mm"
include "eqid.mm"
include "toptopon.mm"
include "kqtopon.mm"
include "sylbi.mm"
include "topontop.mm"
include "syl.mm"
include "cdm.mm"
include "c0.mm"
include "0opn.mm"
include "elfvdm.mm"
include "cqtop.mm"
include "co.mm"
include "ovex.mm"
include "df-kq.mm"
include "dmmpti.mm"
include "syl6eleq.mm"
include "impbii.mm"

theorem kqtop
  let cJ: class J
  let vo: setvar o
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let va: setvar a
  let vb: setvar b
  let vj: setvar j
  let vw: setvar w
  let vz: setvar z
  let cX: class X


  assert |- ( J e. Top <-> ( KQ ` J ) e. Top )

  proof
    cJ
    ctop
    wcel
    #
    cJ
    ckq
    cfv
    #
    ctop
    wcel
    #
    @0
    @1
    vx
    cJ
    cuni
    #
    vx
    cv
    vy
    cv
    wcel
    #
    vy
    cJ
    crab
    cmpt
    #
    crn
    #
    ctopon
    cfv
    wcel
    #
    @2
    @0
    cJ
    @3
    ctopon
    cfv
    wcel
    @7
    cJ
    @3
    @3
    eqid
    toptopon
    vx
    vy
    @5
    cJ
    @3
    @5
    eqid
    kqtopon
    sylbi
    @6
    @1
    topontop
    syl
    @2
    cJ
    ckq
    cdm
    #
    ctop
    @2
    c0
    @1
    wcel
    cJ
    @8
    wcel
    @1
    0opn
    c0
    cJ
    ckq
    elfvdm
    syl
    vj
    ctop
    vj
    cv
    #
    vx
    @9
    cuni
    @4
    vy
    @9
    crab
    cmpt
    #
    cqtop
    co
    ckq
    @9
    @10
    cqtop
    ovex
    vx
    vy
    vj
    df-kq
    dmmpti
    syl6eleq
    impbii
end
