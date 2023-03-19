include "cusgr.mm"
include "wcel.mm"
include "cedg.mm"
include "cfv.mm"
include "ciedg.mm"
include "crn.mm"
include "cv.mm"
include "chash.mm"
include "c2.mm"
include "wceq.mm"
include "cvtx.mm"
include "cpw.mm"
include "crab.mm"
include "edgval.mm"
include "cdm.mm"
include "wf1.mm"
include "wf.mm"
include "wss.mm"
include "eqid.mm"
include "usgrfs.mm"
include "f1f.mm"
include "frn.mm"
include "3syl.mm"
include "syl5eqss.mm"

theorem usgredgss
  let vx: setvar x
  let cG: class G

  disjoint G x
  assert |- ( G e. USGraph -> ( Edg ` G ) C_ { x e. ~P ( Vtx ` G ) | ( # ` x ) = 2 } )

  proof
    cG
    cusgr
    wcel
    #
    cG
    cedg
    cfv
    cG
    ciedg
    cfv
    #
    crn
    #
    vx
    cv
    chash
    cfv
    c2
    wceq
    vx
    cG
    cvtx
    cfv
    #
    cpw
    crab
    #
    cG
    edgval
    @0
    @1
    cdm
    #
    @4
    @1
    wf1
    @5
    @4
    @1
    wf
    @2
    @4
    wss
    vx
    @1
    cG
    @3
    @3
    eqid
    @1
    eqid
    usgrfs
    @5
    @4
    @1
    f1f
    @5
    @4
    @1
    frn
    3syl
    syl5eqss
end
