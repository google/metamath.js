include "cusp.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cuss.mm"
include "cfv.mm"
include "cxp.mm"
include "crest.mm"
include "co.mm"
include "cust.mm"
include "cress.mm"
include "cvv.mm"
include "wceq.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "ssex.mm"
include "adantl.mm"
include "ressuss.mm"
include "syl.mm"
include "syl5eq.mm"
include "ctopn.mm"
include "cutop.mm"
include "eqid.mm"
include "isusp.mm"
include "simplbi.mm"
include "trust.mm"
include "sylan.mm"
include "eqeltrd.mm"

theorem ressust
  let cA: class A
  let cT: class T
  let cW: class W
  let cX: class X
  assume ressust.x: |- X = ( Base ` W )
  assume ressust.t: |- T = ( UnifSt ` ( W |`s A ) )


  assert |- ( ( W e. UnifSp /\ A C_ X ) -> T e. ( UnifOn ` A ) )

  proof
    cW
    cusp
    wcel
    #
    cA
    cX
    wss
    #
    wa
    #
    cT
    cW
    cuss
    cfv
    #
    cA
    cA
    cxp
    crest
    co
    #
    cA
    cust
    cfv
    #
    @2
    cT
    cW
    cA
    cress
    co
    cuss
    cfv
    #
    @4
    ressust.t
    @2
    cA
    cvv
    wcel
    #
    @6
    @4
    wceq
    @1
    @7
    @0
    cA
    cX
    cX
    cW
    cbs
    cfv
    cvv
    ressust.x
    cW
    cbs
    fvex
    eqeltri
    ssex
    adantl
    cA
    cvv
    cW
    ressuss
    syl
    syl5eq
    @0
    @3
    cX
    cust
    cfv
    wcel
    #
    @1
    @4
    @5
    wcel
    @0
    @8
    cW
    ctopn
    cfv
    #
    @3
    cutop
    cfv
    wceq
    cX
    @3
    @9
    cW
    ressust.x
    @3
    eqid
    @9
    eqid
    isusp
    simplbi
    cA
    @3
    cX
    trust
    sylan
    eqeltrd
end
