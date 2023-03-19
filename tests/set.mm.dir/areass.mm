include "carea.mm"
include "cdm.mm"
include "wcel.mm"
include "cr.mm"
include "cxp.mm"
include "wss.mm"
include "cv.mm"
include "csn.mm"
include "cima.mm"
include "cvol.mm"
include "ccnv.mm"
include "wral.mm"
include "cfv.mm"
include "cmpt.mm"
include "cibl.mm"
include "dmarea.mm"
include "simp1bi.mm"

theorem areass
  let cS: class S
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let cA: class A


  assert |- ( S e. dom area -> S C_ ( RR X. RR ) )

  proof
    cS
    carea
    cdm
    wcel
    cS
    cr
    cr
    cxp
    wss
    cS
    vx
    cv
    csn
    cima
    #
    cvol
    ccnv
    cr
    cima
    wcel
    vx
    cr
    wral
    vx
    cr
    @0
    cvol
    cfv
    cmpt
    cibl
    wcel
    vx
    cS
    dmarea
    simp1bi
end
