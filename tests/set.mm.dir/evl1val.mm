include "ccrg.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "c1o.mm"
include "cmap.mm"
include "co.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "cmpt.mm"
include "ccom.mm"
include "evl1fval.mm"
include "fveq1i.mm"
include "cpws.mm"
include "cbs.mm"
include "wf.mm"
include "wceq.mm"
include "crh.mm"
include "con0.mm"
include "1on.mm"
include "simpl.mm"
include "eqid.mm"
include "evlrhm.mm"
include "sylancr.mm"
include "rhmf.mm"
include "syl.mm"
include "fvco3.mm"
include "sylancom.mm"
include "syl5eq.mm"
include "ffvelrn.mm"
include "crg.mm"
include "cvv.mm"
include "crngring.mm"
include "adantr.mm"
include "ovex.mm"
include "pwsbas.mm"
include "sylancl.mm"
include "eleqtrrd.mm"
include "coeq1.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "coex.mm"
include "fvmpt.mm"
include "eqtrd.mm"

theorem evl1val
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cQ: class Q
  let cR: class R
  let cK: class K
  let cM: class M
  let cO: class O
  let vi: setvar i
  let vr: setvar r
  let vx: setvar x
  let vb: setvar b
  assume evl1fval.o: |- O = ( eval1 ` R )
  assume evl1fval.q: |- Q = ( 1o eval R )
  assume evl1fval.b: |- B = ( Base ` R )
  assume evl1val.m: |- M = ( 1o mPoly R )
  assume evl1val.k: |- K = ( Base ` M )

  disjoint B y
  disjoint i r
  disjoint A x
  disjoint b r
  disjoint b x
  disjoint b y
  disjoint B b
  disjoint r x
  disjoint r y
  disjoint B r
  disjoint x y
  disjoint B x
  disjoint Q b
  disjoint Q r
  disjoint Q x
  disjoint R b
  disjoint R r
  disjoint R x
  assert |- ( ( R e. CRing /\ A e. K ) -> ( O ` A ) = ( ( Q ` A ) o. ( y e. B |-> ( 1o X. { y } ) ) ) )

  proof
    cR
    ccrg
    wcel
    #
    cA
    cK
    wcel
    #
    wa
    #
    cA
    cO
    cfv
    #
    cA
    cQ
    cfv
    #
    vx
    cB
    cB
    c1o
    cmap
    co
    #
    cmap
    co
    #
    vx
    cv
    #
    vy
    cB
    c1o
    vy
    cv
    csn
    cxp
    #
    cmpt
    #
    ccom
    #
    cmpt
    #
    cfv
    #
    @4
    @9
    ccom
    #
    @2
    @3
    cA
    @11
    cQ
    ccom
    #
    cfv
    #
    @12
    cA
    cO
    @14
    vx
    vy
    cB
    cQ
    cR
    cO
    evl1fval.o
    evl1fval.q
    evl1fval.b
    evl1fval
    fveq1i
    @0
    @1
    cK
    cR
    @5
    cpws
    co
    #
    cbs
    cfv
    #
    cQ
    wf
    #
    @15
    @12
    wceq
    @2
    cQ
    cM
    @16
    crh
    co
    wcel
    #
    @18
    @2
    c1o
    con0
    wcel
    @0
    @19
    1on
    @0
    @1
    simpl
    cB
    cQ
    cR
    @16
    c1o
    con0
    cM
    evl1fval.q
    evl1fval.b
    evl1val.m
    @16
    eqid
    #
    evlrhm
    sylancr
    cK
    @17
    cM
    @16
    cQ
    evl1val.k
    @17
    eqid
    rhmf
    syl
    #
    cK
    @17
    cA
    @11
    cQ
    fvco3
    sylancom
    syl5eq
    @2
    @4
    @6
    wcel
    @12
    @13
    wceq
    @2
    @4
    @17
    @6
    @0
    @1
    @18
    @4
    @17
    wcel
    @21
    cK
    @17
    cA
    cQ
    ffvelrn
    sylancom
    @2
    cR
    crg
    wcel
    #
    @5
    cvv
    wcel
    @6
    @17
    wceq
    @0
    @22
    @1
    cR
    crngring
    adantr
    cB
    c1o
    cmap
    ovex
    cB
    cR
    @5
    crg
    cvv
    @16
    @20
    evl1fval.b
    pwsbas
    sylancl
    eleqtrrd
    vx
    @4
    @10
    @13
    @6
    @11
    @7
    @4
    @9
    coeq1
    @11
    eqid
    @4
    @9
    cA
    cQ
    fvex
    vy
    cB
    @8
    cB
    cR
    cbs
    cfv
    cvv
    evl1fval.b
    cR
    cbs
    fvex
    eqeltri
    mptex
    coex
    fvmpt
    syl
    eqtrd
end
