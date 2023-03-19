include "cuhgr.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wrex.mm"
include "cfv.mm"
include "cdm.mm"
include "wb.mm"
include "crn.mm"
include "cedg.mm"
include "ciedg.mm"
include "wceq.mm"
include "edgval.mm"
include "a1i.mm"
include "rneqi.mm"
include "3eqtr4g.mm"
include "rexeqdv.mm"
include "wfn.mm"
include "wfun.mm"
include "uhgrfun.mm"
include "funfn.mm"
include "sylib.mm"
include "eleq2.mm"
include "rexrn.mm"
include "syl.mm"
include "bitrd.mm"
include "adantr.mm"
include "bicomd.mm"

theorem uhgrvtxedgiedgb
  let cU: class U
  let ve: setvar e
  let vi: setvar i
  let cE: class E
  let cG: class G
  let cI: class I
  let cV: class V
  assume uhgrvtxedgiedgb.v: |- V = ( Vtx ` G )
  assume uhgrvtxedgiedgb.i: |- I = ( iEdg ` G )
  assume uhgrvtxedgiedgb.e: |- E = ( Edg ` G )

  disjoint E e
  disjoint I e
  disjoint I i
  disjoint e i
  disjoint U e
  disjoint U i
  assert |- ( ( G e. UHGraph /\ U e. V ) -> ( E. i e. dom I U e. ( I ` i ) <-> E. e e. E U e. e ) )

  proof
    cG
    cuhgr
    wcel
    #
    cU
    cV
    wcel
    #
    wa
    cU
    ve
    cv
    #
    wcel
    #
    ve
    cE
    wrex
    #
    cU
    vi
    cv
    cI
    cfv
    #
    wcel
    #
    vi
    cI
    cdm
    #
    wrex
    #
    @0
    @4
    @8
    wb
    @1
    @0
    @4
    @3
    ve
    cI
    crn
    #
    wrex
    #
    @8
    @0
    @3
    ve
    cE
    @9
    @0
    cG
    cedg
    cfv
    #
    cG
    ciedg
    cfv
    #
    crn
    #
    cE
    @9
    @11
    @13
    wceq
    @0
    cG
    edgval
    a1i
    uhgrvtxedgiedgb.e
    cI
    @12
    uhgrvtxedgiedgb.i
    rneqi
    3eqtr4g
    rexeqdv
    @0
    cI
    @7
    wfn
    #
    @10
    @8
    wb
    @0
    cI
    wfun
    @14
    cI
    cG
    uhgrvtxedgiedgb.i
    uhgrfun
    cI
    funfn
    sylib
    @3
    @6
    ve
    vi
    @7
    cI
    @2
    @5
    cU
    eleq2
    rexrn
    syl
    bitrd
    adantr
    bicomd
end
