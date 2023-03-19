include "crdg.mm"
include "cdm.mm"
include "wcel.mm"
include "cres.mm"
include "cvv.mm"
include "cv.mm"
include "c0.mm"
include "wceq.mm"
include "wlim.mm"
include "crn.mm"
include "cuni.mm"
include "cfv.mm"
include "cif.mm"
include "cmpt.mm"
include "crecs.mm"
include "df-rdg.mm"
include "reseq1i.mm"
include "wfn.mm"
include "wral.mm"
include "wa.mm"
include "con0.mm"
include "wrex.mm"
include "cab.mm"
include "rdglem1.mm"
include "tfrlem9a.mm"
include "dmeqi.mm"
include "eleq2s.mm"
include "syl5eqel.mm"

theorem rdgseg
  let cA: class A
  let cB: class B
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vg: setvar g
  let vv: setvar v
  let vw: setvar w


  assert |- ( B e. dom rec ( F , A ) -> ( rec ( F , A ) |` B ) e. _V )

  proof
    cB
    cF
    cA
    crdg
    #
    cdm
    #
    wcel
    @0
    cB
    cres
    vg
    cvv
    vg
    cv
    #
    c0
    wceq
    cA
    @2
    cdm
    #
    wlim
    @2
    crn
    cuni
    @3
    cuni
    @2
    cfv
    cF
    cfv
    cif
    cif
    cmpt
    #
    crecs
    #
    cB
    cres
    #
    cvv
    @0
    @5
    cB
    vg
    cF
    cA
    df-rdg
    #
    reseq1i
    @6
    cvv
    wcel
    cB
    @5
    cdm
    @1
    vx
    vy
    vw
    cv
    #
    vy
    cv
    #
    wfn
    vv
    cv
    #
    @8
    cfv
    @8
    @10
    cres
    @4
    cfv
    wceq
    vv
    @9
    wral
    wa
    vy
    con0
    wrex
    vw
    cab
    cB
    vf
    @4
    vy
    vv
    vx
    vy
    vw
    vf
    @4
    rdglem1
    tfrlem9a
    @0
    @5
    @7
    dmeqi
    eleq2s
    syl5eqel
end
