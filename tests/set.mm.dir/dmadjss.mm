include "cado.mm"
include "cdm.mm"
include "cv.mm"
include "chil.mm"
include "cmap.mm"
include "co.mm"
include "wcel.mm"
include "wf.mm"
include "cfv.mm"
include "csp.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "copab.mm"
include "w3a.mm"
include "dfadj2.mm"
include "3anass.mm"
include "ax-hilex.mm"
include "elmap.mm"
include "anbi1i.mm"
include "bitr4i.mm"
include "opabbii.mm"
include "eqtri.mm"
include "dmeqi.mm"
include "dmopabss.mm"
include "eqsstri.mm"

theorem dmadjss
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cT: class T


  assert |- dom adjh C_ ( ~H ^m ~H )

  proof
    cado
    cdm
    vt
    cv
    #
    chil
    chil
    cmap
    co
    #
    wcel
    #
    chil
    chil
    vu
    cv
    #
    wf
    #
    vx
    cv
    #
    vy
    cv
    #
    @0
    cfv
    csp
    co
    @5
    @3
    cfv
    @6
    csp
    co
    wceq
    vy
    chil
    wral
    vx
    chil
    wral
    #
    wa
    #
    wa
    #
    vt
    vu
    copab
    #
    cdm
    @1
    cado
    @10
    cado
    chil
    chil
    @0
    wf
    #
    @4
    @7
    w3a
    #
    vt
    vu
    copab
    @10
    vx
    vy
    vu
    vt
    dfadj2
    @12
    @9
    vt
    vu
    @12
    @11
    @8
    wa
    @9
    @11
    @4
    @7
    3anass
    @2
    @11
    @8
    chil
    chil
    @0
    ax-hilex
    ax-hilex
    elmap
    anbi1i
    bitr4i
    opabbii
    eqtri
    dmeqi
    @8
    vt
    vu
    @1
    dmopabss
    eqsstri
end
