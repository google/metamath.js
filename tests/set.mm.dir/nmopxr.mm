include "chil.mm"
include "wf.mm"
include "cnop.mm"
include "cfv.mm"
include "cv.mm"
include "cno.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "cab.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "nmopval.mm"
include "wss.mm"
include "wcel.mm"
include "cr.mm"
include "nmopsetretHIL.mm"
include "ressxr.mm"
include "syl6ss.mm"
include "supxrcl.mm"
include "syl.mm"
include "eqeltrd.mm"

theorem nmopxr
  let cT: class T
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( T : ~H --> ~H -> ( normop ` T ) e. RR* )

  proof
    chil
    chil
    cT
    wf
    #
    cT
    cnop
    cfv
    vy
    cv
    #
    cno
    cfv
    c1
    cle
    wbr
    vx
    cv
    @1
    cT
    cfv
    cno
    cfv
    wceq
    wa
    vy
    chil
    wrex
    vx
    cab
    #
    cxr
    clt
    csup
    #
    cxr
    vx
    vy
    cT
    nmopval
    @0
    @2
    cxr
    wss
    @3
    cxr
    wcel
    @0
    @2
    cr
    cxr
    vx
    vy
    cT
    nmopsetretHIL
    ressxr
    syl6ss
    @2
    supxrcl
    syl
    eqeltrd
end
