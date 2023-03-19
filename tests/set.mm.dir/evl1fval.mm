include "cvv.mm"
include "wcel.mm"
include "c1o.mm"
include "cmap.mm"
include "co.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "cmpt.mm"
include "ccom.mm"
include "wceq.mm"
include "ce1.mm"
include "cfv.mm"
include "cbs.mm"
include "cevl.mm"
include "csb.mm"
include "fvexd.mm"
include "wa.mm"
include "id.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "sylan9eqr.mm"
include "oveq1d.mm"
include "oveq12d.mm"
include "mpteq1d.mm"
include "coeq2d.mm"
include "mpteq12dv.mm"
include "simpl.mm"
include "oveq2d.mm"
include "coeq12d.mm"
include "csbied.mm"
include "df-evl1.mm"
include "ovex.mm"
include "mptex.mm"
include "eqeltri.mm"
include "coex.mm"
include "fvmpt.mm"
include "syl5eq.mm"
include "wn.mm"
include "c0.mm"
include "fvprc.mm"
include "co02.mm"
include "ces.mm"
include "df-evl.mm"
include "reldmmpt2.mm"
include "ovprc2.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"

theorem evl1fval
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cQ: class Q
  let cR: class R
  let cO: class O
  let vi: setvar i
  let vr: setvar r
  let cA: class A
  let vb: setvar b
  assume evl1fval.o: |- O = ( eval1 ` R )
  assume evl1fval.q: |- Q = ( 1o eval R )
  assume evl1fval.b: |- B = ( Base ` R )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint Q x
  disjoint R x
  disjoint i r
  disjoint A x
  disjoint b r
  disjoint b x
  disjoint b y
  disjoint B b
  disjoint r x
  disjoint r y
  disjoint B r
  disjoint Q b
  disjoint Q r
  disjoint R b
  disjoint R r
  assert |- O = ( ( x e. ( B ^m ( B ^m 1o ) ) |-> ( x o. ( y e. B |-> ( 1o X. { y } ) ) ) ) o. Q )

  proof
    cR
    cvv
    wcel
    #
    cO
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
    cQ
    ccom
    #
    wceq
    @0
    cO
    cR
    ce1
    cfv
    #
    @8
    evl1fval.o
    vr
    cR
    vb
    vr
    cv
    #
    cbs
    cfv
    #
    vx
    vb
    cv
    #
    @12
    c1o
    cmap
    co
    #
    cmap
    co
    #
    @3
    vy
    @12
    @4
    cmpt
    #
    ccom
    #
    cmpt
    #
    c1o
    @10
    cevl
    co
    #
    ccom
    #
    csb
    @8
    cvv
    ce1
    @10
    cR
    wceq
    #
    vb
    @11
    @19
    @8
    cvv
    @20
    @10
    cbs
    fvexd
    @20
    @12
    @11
    wceq
    #
    wa
    #
    @17
    @7
    @18
    cQ
    @22
    vx
    @14
    @16
    @2
    @6
    @22
    @12
    cB
    @13
    @1
    cmap
    @21
    @20
    @12
    @11
    cB
    @21
    id
    @20
    @11
    cR
    cbs
    cfv
    cB
    @10
    cR
    cbs
    fveq2
    evl1fval.b
    syl6eqr
    sylan9eqr
    #
    @22
    @12
    cB
    c1o
    cmap
    @23
    oveq1d
    oveq12d
    @22
    @15
    @5
    @3
    @22
    vy
    @12
    cB
    @4
    @23
    mpteq1d
    coeq2d
    mpteq12dv
    @22
    @18
    c1o
    cR
    cevl
    co
    #
    cQ
    @22
    @10
    cR
    c1o
    cevl
    @20
    @21
    simpl
    oveq2d
    evl1fval.q
    syl6eqr
    coeq12d
    csbied
    vx
    vy
    vr
    vb
    df-evl1
    @7
    cQ
    vx
    @2
    @6
    cB
    @1
    cmap
    ovex
    mptex
    cQ
    @24
    cvv
    evl1fval.q
    c1o
    cR
    cevl
    ovex
    eqeltri
    coex
    fvmpt
    syl5eq
    @0
    wn
    #
    cO
    @7
    c0
    ccom
    #
    @8
    @25
    cO
    c0
    @26
    @25
    cO
    @9
    c0
    evl1fval.o
    cR
    ce1
    fvprc
    syl5eq
    @7
    co02
    syl6eqr
    @25
    cQ
    c0
    @7
    @25
    cQ
    @24
    c0
    evl1fval.q
    c1o
    cR
    cevl
    vi
    vr
    cvv
    cvv
    @11
    vi
    cv
    @10
    ces
    co
    cfv
    cevl
    vi
    vr
    df-evl
    reldmmpt2
    ovprc2
    syl5eq
    coeq2d
    eqtr4d
    pm2.61i
end
