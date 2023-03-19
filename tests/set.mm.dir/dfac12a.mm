include "wac.mm"
include "cr1.mm"
include "con0.mm"
include "cima.mm"
include "cuni.mm"
include "ccrd.mm"
include "cdm.mm"
include "wss.mm"
include "cv.mm"
include "cpw.mm"
include "wcel.mm"
include "wral.mm"
include "cvv.mm"
include "wceq.mm"
include "ssv.mm"
include "eqss.mm"
include "mpbiran.mm"
include "dfac10.mm"
include "unir1.mm"
include "sseq1i.mm"
include "3bitr4i.mm"
include "dfac12r.mm"
include "bitr4i.mm"

theorem dfac12a
  let vx: setvar x
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vy: setvar y
  let vz: setvar z


  assert |- ( CHOICE <-> A. x e. On ~P x e. dom card )

  proof
    wac
    cr1
    con0
    cima
    cuni
    #
    ccrd
    cdm
    #
    wss
    #
    vx
    cv
    cpw
    @1
    wcel
    vx
    con0
    wral
    @1
    cvv
    wceq
    #
    cvv
    @1
    wss
    #
    wac
    @2
    @3
    @1
    cvv
    wss
    @4
    @1
    ssv
    @1
    cvv
    eqss
    mpbiran
    dfac10
    @0
    cvv
    @1
    unir1
    sseq1i
    3bitr4i
    vx
    dfac12r
    bitr4i
end
