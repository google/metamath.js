include "chil.mm"
include "cc.mm"
include "wf.mm"
include "cnmf.mm"
include "cfv.mm"
include "cv.mm"
include "cno.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "cabs.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "cab.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "nmfnval.mm"
include "wss.mm"
include "wcel.mm"
include "cr.mm"
include "nmfnsetre.mm"
include "ressxr.mm"
include "syl6ss.mm"
include "supxrcl.mm"
include "syl.mm"
include "eqeltrd.mm"

theorem nmfnxr
  let cT: class T
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( T : ~H --> CC -> ( normfn ` T ) e. RR* )

  proof
    chil
    cc
    cT
    wf
    #
    cT
    cnmf
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
    cabs
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
    nmfnval
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
    nmfnsetre
    ressxr
    syl6ss
    @2
    supxrcl
    syl
    eqeltrd
end
