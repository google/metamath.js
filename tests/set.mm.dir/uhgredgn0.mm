include "cuhgr.mm"
include "wcel.mm"
include "cedg.mm"
include "cfv.mm"
include "cvtx.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "ciedg.mm"
include "crn.mm"
include "edgval.mm"
include "cdm.mm"
include "wf.mm"
include "wss.mm"
include "eqid.mm"
include "uhgrf.mm"
include "frn.mm"
include "syl.mm"
include "syl5eqss.mm"
include "sselda.mm"

theorem uhgredgn0
  let cE: class E
  let cG: class G


  assert |- ( ( G e. UHGraph /\ E e. ( Edg ` G ) ) -> E e. ( ~P ( Vtx ` G ) \ { (/) } ) )

  proof
    cG
    cuhgr
    wcel
    #
    cG
    cedg
    cfv
    #
    cG
    cvtx
    cfv
    #
    cpw
    c0
    csn
    cdif
    #
    cE
    @0
    @1
    cG
    ciedg
    cfv
    #
    crn
    #
    @3
    cG
    edgval
    @0
    @4
    cdm
    #
    @3
    @4
    wf
    @5
    @3
    wss
    @4
    cG
    @2
    @2
    eqid
    @4
    eqid
    uhgrf
    @6
    @3
    @4
    frn
    syl
    syl5eqss
    sselda
end
