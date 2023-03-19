include "cupgr.mm"
include "wcel.mm"
include "cedg.mm"
include "cfv.mm"
include "ciedg.mm"
include "crn.mm"
include "cv.mm"
include "chash.mm"
include "c2.mm"
include "cle.mm"
include "wbr.mm"
include "cvtx.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "crab.mm"
include "edgval.mm"
include "cdm.mm"
include "wf.mm"
include "wss.mm"
include "eqid.mm"
include "upgrf.mm"
include "frn.mm"
include "syl.mm"
include "syl5eqss.mm"

theorem upgredgss
  let vx: setvar x
  let cG: class G

  disjoint G x
  assert |- ( G e. UPGraph -> ( Edg ` G ) C_ { x e. ( ~P ( Vtx ` G ) \ { (/) } ) | ( # ` x ) <_ 2 } )

  proof
    cG
    cupgr
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
    cle
    wbr
    vx
    cG
    cvtx
    cfv
    #
    cpw
    c0
    csn
    cdif
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
    upgrf
    @5
    @4
    @1
    frn
    syl
    syl5eqss
end
