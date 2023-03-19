include "cbrsiga.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "csigagen.mm"
include "ctop.mm"
include "cima.mm"
include "df-brsiga.mm"
include "wcel.mm"
include "retop.mm"
include "wfun.mm"
include "cdm.mm"
include "wi.mm"
include "cvv.mm"
include "cv.mm"
include "wss.mm"
include "cuni.mm"
include "csiga.mm"
include "crab.mm"
include "cint.mm"
include "df-sigagen.mm"
include "funmpt2.mm"
include "c0.mm"
include "fvex.mm"
include "sigagensiga.mm"
include "elrnsiga.mm"
include "mp2b.mm"
include "0elsiga.mm"
include "elfvdm.mm"
include "funfvima.mm"
include "mp2an.mm"
include "ax-mp.mm"
include "eqeltri.mm"

theorem brsiga
  let vs: setvar s
  let vx: setvar x


  assert |- BrSiga e. ( sigaGen " Top )

  proof
    cbrsiga
    cioo
    crn
    #
    ctg
    cfv
    #
    csigagen
    cfv
    #
    csigagen
    ctop
    cima
    #
    df-brsiga
    @1
    ctop
    wcel
    #
    @2
    @3
    wcel
    #
    retop
    csigagen
    wfun
    @1
    csigagen
    cdm
    wcel
    #
    @4
    @5
    wi
    vx
    cvv
    vx
    cv
    #
    vs
    cv
    wss
    vs
    @7
    cuni
    csiga
    cfv
    crab
    cint
    csigagen
    vx
    vs
    df-sigagen
    funmpt2
    @2
    csiga
    crn
    cuni
    wcel
    #
    c0
    @2
    wcel
    @6
    @1
    cvv
    wcel
    @2
    @1
    cuni
    #
    csiga
    cfv
    wcel
    @8
    @0
    ctg
    fvex
    @1
    cvv
    sigagensiga
    @2
    @9
    elrnsiga
    mp2b
    @2
    0elsiga
    c0
    @1
    csigagen
    elfvdm
    mp2b
    ctop
    @1
    csigagen
    funfvima
    mp2an
    ax-mp
    eqeltri
end
