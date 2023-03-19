include "ccmp.mm"
include "cnlly.mm"
include "wcel.mm"
include "ctop.mm"
include "wa.mm"
include "ccn.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt2.mm"
include "cxko.mm"
include "ctx.mm"
include "c1o.mm"
include "csn.mm"
include "cxp.mm"
include "ccom.mm"
include "c0.mm"
include "cpw.mm"
include "ctopon.mm"
include "nllytop.mm"
include "eqid.mm"
include "xkotopon.mm"
include "sylan.mm"
include "adantr.mm"
include "toptopon.mm"
include "sylib.mm"
include "cnmpt1st.mm"
include "cnmpt2nd.mm"
include "cmpt.mm"
include "con0.mm"
include "1on.mm"
include "distopon.mm"
include "mp1i.mm"
include "xkoccn.mm"
include "syl2anc.mm"
include "wceq.mm"
include "sneq.mm"
include "xpeq2d.mm"
include "cnmpt21.mm"
include "distop.mm"
include "simpl.mm"
include "simpr.mm"
include "xkococn.mm"
include "syl3anc.mm"
include "coeq1.mm"
include "coeq2.mm"
include "sylan9eq.mm"
include "cnmpt22.mm"
include "0lt1o.mm"
include "a1i.mm"
include "cuni.mm"
include "unipw.mm"
include "eqcomi.mm"
include "xkopjcn.mm"
include "fveq1.mm"
include "wf.mm"
include "vex.mm"
include "fconst.mm"
include "fvco3.mm"
include "mp2an.mm"
include "fvconst2.mm"
include "ax-mp.mm"
include "fveq2i.mm"
include "eqtri.mm"
include "syl6eq.mm"
include "syl5eqel.mm"

theorem xkofvcn
  let vx: setvar x
  let cR: class R
  let cS: class S
  let vf: setvar f
  let cF: class F
  let cX: class X
  let vg: setvar g
  let vh: setvar h
  let vy: setvar y
  assume xkofvcn.1: |- X = U. R
  assume xkofvcn.2: |- F = ( f e. ( R Cn S ) , x e. X |-> ( f ` x ) )

  disjoint f x
  disjoint R f
  disjoint R x
  disjoint S f
  disjoint S x
  disjoint X f
  disjoint X x
  disjoint f g
  disjoint f h
  disjoint f y
  disjoint g h
  disjoint g x
  disjoint g y
  disjoint R g
  disjoint h x
  disjoint h y
  disjoint R h
  disjoint x y
  disjoint R y
  disjoint S g
  disjoint S h
  disjoint S y
  disjoint X g
  disjoint X h
  disjoint X y
  assert |- ( ( R e. N-Locally Comp /\ S e. Top ) -> F e. ( ( ( S ^ko R ) tX R ) Cn S ) )

  proof
    cR
    ccmp
    cnlly
    wcel
    #
    cS
    ctop
    wcel
    #
    wa
    #
    cF
    vf
    vx
    cR
    cS
    ccn
    co
    #
    cX
    vx
    cv
    #
    vf
    cv
    #
    cfv
    #
    cmpt2
    cS
    cR
    cxko
    co
    #
    cR
    ctx
    co
    cS
    ccn
    co
    xkofvcn.2
    @2
    vf
    vx
    vg
    @5
    c1o
    @4
    csn
    #
    cxp
    #
    ccom
    #
    c0
    vg
    cv
    #
    cfv
    #
    @6
    @7
    cR
    cS
    c1o
    cpw
    #
    cxko
    co
    #
    cS
    @3
    cX
    @13
    cS
    ccn
    co
    #
    @0
    cR
    ctop
    wcel
    #
    @1
    @7
    @3
    ctopon
    cfv
    wcel
    ccmp
    cR
    nllytop
    #
    cR
    cS
    @7
    @7
    eqid
    xkotopon
    sylan
    #
    @2
    @16
    cR
    cX
    ctopon
    cfv
    wcel
    #
    @0
    @16
    @1
    @17
    adantr
    #
    cR
    cX
    xkofvcn.1
    toptopon
    sylib
    #
    @2
    vf
    vx
    vg
    vh
    @5
    @9
    @11
    vh
    cv
    #
    ccom
    #
    @10
    @7
    cR
    @7
    cR
    @13
    cxko
    co
    #
    @14
    @13
    cR
    ccn
    co
    #
    @3
    cX
    @3
    @18
    @21
    @2
    vf
    vx
    @7
    cR
    @3
    cX
    @18
    @21
    cnmpt1st
    @2
    vf
    vx
    vy
    @4
    c1o
    vy
    cv
    #
    csn
    #
    cxp
    #
    @9
    @7
    cR
    cR
    @24
    @3
    cX
    cX
    @18
    @21
    @2
    vf
    vx
    @7
    cR
    @3
    cX
    @18
    @21
    cnmpt2nd
    @21
    @2
    @13
    c1o
    ctopon
    cfv
    wcel
    #
    @19
    vy
    cX
    @28
    cmpt
    cR
    @24
    ccn
    co
    wcel
    c1o
    con0
    wcel
    #
    @29
    @2
    1on
    c1o
    con0
    distopon
    mp1i
    @21
    vy
    @13
    cR
    c1o
    cX
    xkoccn
    syl2anc
    @26
    @4
    wceq
    @27
    @8
    c1o
    @26
    @4
    sneq
    xpeq2d
    cnmpt21
    @18
    @2
    @13
    ctop
    wcel
    #
    @16
    @24
    @25
    ctopon
    cfv
    wcel
    @30
    @31
    @2
    1on
    c1o
    con0
    distop
    mp1i
    #
    @20
    @13
    cR
    @24
    @24
    eqid
    xkotopon
    syl2anc
    @2
    @31
    @0
    @1
    vg
    vh
    @3
    @25
    @23
    cmpt2
    #
    @7
    @24
    ctx
    co
    @14
    ccn
    co
    wcel
    @32
    @0
    @1
    simpl
    @0
    @1
    simpr
    #
    @13
    cR
    cS
    vg
    vh
    @33
    @33
    eqid
    xkococn
    syl3anc
    @11
    @5
    wceq
    @22
    @9
    wceq
    @23
    @5
    @22
    ccom
    @10
    @11
    @5
    @22
    coeq1
    @22
    @9
    @5
    coeq2
    sylan9eq
    cnmpt22
    @2
    @31
    @1
    @14
    @15
    ctopon
    cfv
    wcel
    @32
    @34
    @13
    cS
    @14
    @14
    eqid
    xkotopon
    syl2anc
    @2
    @31
    @1
    c0
    c1o
    wcel
    #
    vg
    @15
    @12
    cmpt
    @14
    cS
    ccn
    co
    wcel
    @32
    @34
    @35
    @2
    0lt1o
    a1i
    c0
    @13
    cS
    vg
    c1o
    @13
    cuni
    c1o
    c1o
    unipw
    eqcomi
    xkopjcn
    syl3anc
    @11
    @10
    wceq
    @12
    c0
    @10
    cfv
    #
    @6
    c0
    @11
    @10
    fveq1
    @36
    c0
    @9
    cfv
    #
    @5
    cfv
    #
    @6
    c1o
    @8
    @9
    wf
    @35
    @36
    @38
    wceq
    c1o
    @4
    vx
    vex
    #
    fconst
    0lt1o
    c1o
    @8
    c0
    @5
    @9
    fvco3
    mp2an
    @37
    @4
    @5
    @35
    @37
    @4
    wceq
    0lt1o
    c1o
    @4
    c0
    @39
    fvconst2
    ax-mp
    fveq2i
    eqtri
    syl6eq
    cnmpt21
    syl5eqel
end
