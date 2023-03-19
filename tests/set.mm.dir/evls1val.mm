include "ccrg.mm"
include "wcel.mm"
include "csubrg.mm"
include "cfv.mm"
include "w3a.mm"
include "c1o.mm"
include "cmap.mm"
include "co.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "cmpt.mm"
include "ccom.mm"
include "wceq.mm"
include "wa.mm"
include "cpw.mm"
include "wss.mm"
include "subrgss.mm"
include "adantl.mm"
include "wb.mm"
include "elpwg.mm"
include "mpbird.mm"
include "evls1fval.mm"
include "syldan.mm"
include "fveq1d.mm"
include "3adant3.mm"
include "cpws.mm"
include "cbs.mm"
include "wf.mm"
include "crh.mm"
include "con0.mm"
include "1on.mm"
include "a1i.mm"
include "simp1.mm"
include "simp2.mm"
include "cress.mm"
include "ces.mm"
include "fveq1i.mm"
include "eqid.mm"
include "evlsrhm.mm"
include "syl3anc.mm"
include "rhmf.mm"
include "syl.mm"
include "simp3.mm"
include "fvco3.mm"
include "syl2anc.mm"
include "ffvelrnd.mm"
include "cvv.mm"
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
include "3eqtrd.mm"

theorem evls1val
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cE: class E
  let cK: class K
  let cM: class M
  let vb: setvar b
  let vr: setvar r
  let vs: setvar s
  let vx: setvar x
  assume evls1fval.q: |- Q = ( S evalSub1 R )
  assume evls1fval.e: |- E = ( 1o evalSub S )
  assume evls1fval.b: |- B = ( Base ` S )
  assume evls1val.m: |- M = ( 1o mPoly ( S |`s R ) )
  assume evls1val.k: |- K = ( Base ` M )

  disjoint B y
  disjoint B b
  disjoint B r
  disjoint B s
  disjoint B x
  disjoint b r
  disjoint b s
  disjoint b x
  disjoint b y
  disjoint r s
  disjoint r x
  disjoint r y
  disjoint s x
  disjoint s y
  disjoint x y
  disjoint E r
  disjoint E s
  disjoint R b
  disjoint R r
  disjoint R s
  disjoint S b
  disjoint S r
  disjoint S s
  disjoint A x
  disjoint E x
  disjoint R x
  assert |- ( ( S e. CRing /\ R e. ( SubRing ` S ) /\ A e. K ) -> ( Q ` A ) = ( ( ( E ` R ) ` A ) o. ( y e. B |-> ( 1o X. { y } ) ) ) )

  proof
    cS
    ccrg
    wcel
    #
    cR
    cS
    csubrg
    cfv
    #
    wcel
    #
    cA
    cK
    wcel
    #
    w3a
    #
    cA
    cQ
    cfv
    #
    cA
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
    cR
    cE
    cfv
    #
    ccom
    #
    cfv
    #
    cA
    @13
    cfv
    #
    @12
    cfv
    #
    @16
    @10
    ccom
    #
    @0
    @2
    @5
    @15
    wceq
    @3
    @0
    @2
    wa
    #
    cA
    cQ
    @14
    @0
    @2
    cR
    cB
    cpw
    wcel
    #
    cQ
    @14
    wceq
    @19
    @20
    cR
    cB
    wss
    #
    @2
    @21
    @0
    cR
    cB
    cS
    evls1fval.b
    subrgss
    adantl
    @2
    @20
    @21
    wb
    @0
    cR
    cB
    @1
    elpwg
    adantl
    mpbird
    vx
    vy
    cB
    cQ
    cR
    cS
    cE
    ccrg
    evls1fval.q
    evls1fval.e
    evls1fval.b
    evls1fval
    syldan
    fveq1d
    3adant3
    @4
    cK
    cS
    @6
    cpws
    co
    #
    cbs
    cfv
    #
    @13
    wf
    #
    @3
    @15
    @17
    wceq
    @4
    @13
    cM
    @22
    crh
    co
    wcel
    #
    @24
    @4
    c1o
    con0
    wcel
    #
    @0
    @2
    @25
    @26
    @4
    1on
    a1i
    @0
    @2
    @3
    simp1
    #
    @0
    @2
    @3
    simp2
    cB
    @13
    cR
    cS
    @22
    cS
    cR
    cress
    co
    #
    c1o
    con0
    cM
    cR
    cE
    c1o
    cS
    ces
    co
    evls1fval.e
    fveq1i
    evls1val.m
    @28
    eqid
    @22
    eqid
    #
    evls1fval.b
    evlsrhm
    syl3anc
    cK
    @23
    cM
    @22
    @13
    evls1val.k
    @23
    eqid
    rhmf
    syl
    #
    @0
    @2
    @3
    simp3
    #
    cK
    @23
    cA
    @12
    @13
    fvco3
    syl2anc
    @4
    @16
    @7
    wcel
    @17
    @18
    wceq
    @4
    @16
    @23
    @7
    @4
    cK
    @23
    cA
    @13
    @30
    @31
    ffvelrnd
    @4
    @0
    @6
    cvv
    wcel
    @7
    @23
    wceq
    @27
    cB
    c1o
    cmap
    ovex
    cB
    cS
    @6
    ccrg
    cvv
    @22
    @29
    evls1fval.b
    pwsbas
    sylancl
    eleqtrrd
    vx
    @16
    @11
    @18
    @7
    @12
    @8
    @16
    @10
    coeq1
    @12
    eqid
    @16
    @10
    cA
    @13
    fvex
    vy
    cB
    @9
    cB
    cS
    cbs
    cfv
    cvv
    evls1fval.b
    cS
    cbs
    fvex
    eqeltri
    mptex
    coex
    fvmpt
    syl
    3eqtrd
end
