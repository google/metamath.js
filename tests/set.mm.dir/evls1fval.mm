include "wcel.mm"
include "cpw.mm"
include "wa.mm"
include "ces1.mm"
include "co.mm"
include "c1o.mm"
include "cmap.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "cmpt.mm"
include "ccom.mm"
include "cfv.mm"
include "cvv.mm"
include "wceq.mm"
include "elex.mm"
include "adantr.mm"
include "simpr.mm"
include "ovex.mm"
include "mptex.mm"
include "fvex.mm"
include "coex.mm"
include "a1i.mm"
include "cbs.mm"
include "ces.mm"
include "csb.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "csbeq1d.mm"
include "eqeltri.mm"
include "id.mm"
include "oveq1.mm"
include "oveq12d.mm"
include "mpteq1.mm"
include "coeq2d.mm"
include "mpteq12dv.mm"
include "coeq1d.mm"
include "adantl.mm"
include "csbied.mm"
include "oveq2.mm"
include "fveq12d.mm"
include "3eqtrd.mm"
include "pweqd.mm"
include "df-evls1.mm"
include "ovmpt2x.mm"
include "syl3anc.mm"
include "syl5eq.mm"

theorem evls1fval
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cE: class E
  let cV: class V
  let vb: setvar b
  let vr: setvar r
  let vs: setvar s
  assume evls1fval.q: |- Q = ( S evalSub1 R )
  assume evls1fval.e: |- E = ( 1o evalSub S )
  assume evls1fval.b: |- B = ( Base ` S )

  disjoint B x
  disjoint B y
  disjoint x y
  disjoint B b
  disjoint B r
  disjoint B s
  disjoint b r
  disjoint b s
  disjoint b x
  disjoint b y
  disjoint r s
  disjoint r x
  disjoint r y
  disjoint s x
  disjoint s y
  disjoint E r
  disjoint E s
  disjoint R b
  disjoint R r
  disjoint R s
  disjoint S b
  disjoint S r
  disjoint S s
  assert |- ( ( S e. V /\ R e. ~P B ) -> Q = ( ( x e. ( B ^m ( B ^m 1o ) ) |-> ( x o. ( y e. B |-> ( 1o X. { y } ) ) ) ) o. ( E ` R ) ) )

  proof
    cS
    cV
    wcel
    #
    cR
    cB
    cpw
    #
    wcel
    #
    wa
    #
    cQ
    cS
    cR
    ces1
    co
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
    cR
    cE
    cfv
    #
    ccom
    #
    evls1fval.q
    @3
    cS
    cvv
    wcel
    #
    @2
    @13
    cvv
    wcel
    #
    @4
    @13
    wceq
    @0
    @14
    @2
    cS
    cV
    elex
    adantr
    @0
    @2
    simpr
    @15
    @3
    @11
    @12
    vx
    @6
    @10
    cB
    @5
    cmap
    ovex
    mptex
    cR
    cE
    fvex
    coex
    a1i
    vs
    vr
    cS
    cR
    cvv
    vs
    cv
    #
    cbs
    cfv
    #
    cpw
    vb
    @17
    vx
    vb
    cv
    #
    @18
    c1o
    cmap
    co
    #
    cmap
    co
    #
    @7
    vy
    @18
    @8
    cmpt
    #
    ccom
    #
    cmpt
    #
    vr
    cv
    #
    c1o
    @16
    ces
    co
    #
    cfv
    #
    ccom
    #
    csb
    #
    @13
    ces1
    cvv
    @1
    @16
    cS
    wceq
    #
    @24
    cR
    wceq
    #
    wa
    #
    @28
    vb
    cB
    @27
    csb
    @11
    @26
    ccom
    #
    @13
    @31
    vb
    @17
    cB
    @27
    @31
    @17
    cS
    cbs
    cfv
    #
    cB
    @29
    @17
    @33
    wceq
    @30
    @16
    cS
    cbs
    fveq2
    #
    adantr
    evls1fval.b
    syl6eqr
    csbeq1d
    @31
    vb
    cB
    @27
    @32
    cvv
    cB
    cvv
    wcel
    @31
    cB
    @33
    cvv
    evls1fval.b
    cS
    cbs
    fvex
    eqeltri
    a1i
    @18
    cB
    wceq
    #
    @27
    @32
    wceq
    @31
    @35
    @23
    @11
    @26
    @35
    vx
    @20
    @22
    @6
    @10
    @35
    @18
    cB
    @19
    @5
    cmap
    @35
    id
    @18
    cB
    c1o
    cmap
    oveq1
    oveq12d
    @35
    @21
    @9
    @7
    vy
    @18
    cB
    @8
    mpteq1
    coeq2d
    mpteq12dv
    coeq1d
    adantl
    csbied
    @31
    @26
    @12
    @11
    @31
    @24
    cR
    @25
    cE
    @29
    @25
    cE
    wceq
    @30
    @29
    @25
    c1o
    cS
    ces
    co
    cE
    @16
    cS
    c1o
    ces
    oveq2
    evls1fval.e
    syl6eqr
    adantr
    @29
    @30
    simpr
    fveq12d
    coeq2d
    3eqtrd
    @29
    @17
    cB
    @29
    @17
    @33
    cB
    @34
    evls1fval.b
    syl6eqr
    pweqd
    vx
    vy
    vs
    vr
    vb
    df-evls1
    ovmpt2x
    syl3anc
    syl5eq
end
