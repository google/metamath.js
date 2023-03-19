include "wcel.mm"
include "csca.mm"
include "cfv.mm"
include "cbs.mm"
include "cmap.mm"
include "co.mm"
include "cpw.mm"
include "w3a.mm"
include "clinc.mm"
include "cv.mm"
include "cvsca.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cmpt2.mm"
include "wceq.mm"
include "lincop.mm"
include "3ad2ant1.mm"
include "oveqd.mm"
include "cvv.mm"
include "simp2.mm"
include "simp3.mm"
include "ovexd.mm"
include "wa.mm"
include "simpr.mm"
include "fveq1.mm"
include "oveq1d.mm"
include "adantr.mm"
include "mpteq12dv.mm"
include "oveq2d.mm"
include "oveq2.mm"
include "eqid.mm"
include "ovmpt2x2.mm"
include "syl3anc.mm"
include "eqtrd.mm"

theorem lincval
  let vx: setvar x
  let cS: class S
  let cM: class M
  let cV: class V
  let cX: class X
  let vm: setvar m
  let vs: setvar s
  let vv: setvar v
  let vk: setvar k

  disjoint M x
  disjoint S x
  disjoint V x
  disjoint M m
  disjoint M s
  disjoint M v
  disjoint m s
  disjoint m v
  disjoint m x
  disjoint s v
  disjoint s x
  disjoint v x
  disjoint X m
  disjoint X v
  disjoint S s
  disjoint S v
  disjoint V s
  disjoint V v
  disjoint k x
  assert |- ( ( M e. X /\ S e. ( ( Base ` ( Scalar ` M ) ) ^m V ) /\ V e. ~P ( Base ` M ) ) -> ( S ( linC ` M ) V ) = ( M gsum ( x e. V |-> ( ( S ` x ) ( .s ` M ) x ) ) ) )

  proof
    cM
    cX
    wcel
    #
    cS
    cM
    csca
    cfv
    cbs
    cfv
    #
    cV
    cmap
    co
    #
    wcel
    #
    cV
    cM
    cbs
    cfv
    cpw
    #
    wcel
    #
    w3a
    #
    cS
    cV
    cM
    clinc
    cfv
    #
    co
    cS
    cV
    vs
    vv
    @1
    vv
    cv
    #
    cmap
    co
    #
    @4
    cM
    vx
    @8
    vx
    cv
    #
    vs
    cv
    #
    cfv
    #
    @10
    cM
    cvsca
    cfv
    #
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt2
    #
    co
    #
    cM
    vx
    cV
    @10
    cS
    cfv
    #
    @10
    @13
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @6
    @7
    @17
    cS
    cV
    @0
    @3
    @7
    @17
    wceq
    @5
    vx
    vv
    cM
    cX
    vs
    lincop
    3ad2ant1
    oveqd
    @6
    @3
    @5
    @22
    cvv
    wcel
    @18
    @22
    wceq
    @0
    @3
    @5
    simp2
    @0
    @3
    @5
    simp3
    @6
    cM
    @21
    cgsu
    ovexd
    vs
    vv
    cS
    cV
    @9
    @4
    @16
    @22
    @17
    cvv
    @2
    @11
    cS
    wceq
    #
    @8
    cV
    wceq
    #
    wa
    #
    @15
    @21
    cM
    cgsu
    @25
    vx
    @8
    @14
    cV
    @20
    @23
    @24
    simpr
    @23
    @14
    @20
    wceq
    @24
    @23
    @12
    @19
    @10
    @13
    @10
    @11
    cS
    fveq1
    oveq1d
    adantr
    mpteq12dv
    oveq2d
    @8
    cV
    @1
    cmap
    oveq2
    @17
    eqid
    ovmpt2x2
    syl3anc
    eqtrd
end
