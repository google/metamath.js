include "cc.mm"
include "wcel.mm"
include "cv.mm"
include "cabs.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "cmul.mm"
include "co.mm"
include "wa.mm"
include "wrex.mm"
include "cc0.mm"
include "fveq2.mm"
include "abs0.mm"
include "syl6eq.mm"
include "oveq2.mm"
include "eqeq12d.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "wne.mm"
include "ccj.mm"
include "cdiv.mm"
include "simpl.mm"
include "cjcld.mm"
include "cr.mm"
include "abscl.mm"
include "adantr.mm"
include "recnd.mm"
include "abs00.mm"
include "necon3bid.mm"
include "biimpar.mm"
include "divcld.mm"
include "absdiv.mm"
include "syl3anc.mm"
include "abscj.mm"
include "absidm.mm"
include "oveq12d.mm"
include "dividd.mm"
include "3eqtrd.mm"
include "divassd.mm"
include "c2.mm"
include "cexp.mm"
include "sqvald.mm"
include "absvalsq.mm"
include "eqtr3d.mm"
include "mvllmuld.mm"
include "mulcomd.mm"
include "3eqtr4d.mm"
include "eqeq1d.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "ci.mm"
include "ax-icn.mm"
include "absi.mm"
include "it0e0.mm"
include "eqcomi.mm"
include "pm3.2i.mm"
include "mp2an.mm"
include "a1i.mm"
include "pm2.61ne.mm"

theorem abs1m
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( A e. CC -> E. x e. CC ( ( abs ` x ) = 1 /\ ( abs ` A ) = ( x x. A ) ) )

  proof
    cA
    cc
    wcel
    #
    vx
    cv
    #
    cabs
    cfv
    #
    c1
    wceq
    #
    cA
    cabs
    cfv
    #
    @1
    cA
    cmul
    co
    #
    wceq
    #
    wa
    #
    vx
    cc
    wrex
    #
    @3
    cc0
    @1
    cc0
    cmul
    co
    #
    wceq
    #
    wa
    #
    vx
    cc
    wrex
    #
    cA
    cc0
    cA
    cc0
    wceq
    #
    @7
    @11
    vx
    cc
    @13
    @6
    @10
    @3
    @13
    @4
    cc0
    @5
    @9
    @13
    @4
    cc0
    cabs
    cfv
    cc0
    cA
    cc0
    cabs
    fveq2
    abs0
    syl6eq
    cA
    cc0
    @1
    cmul
    oveq2
    eqeq12d
    anbi2d
    rexbidv
    @0
    cA
    cc0
    wne
    #
    wa
    #
    cA
    ccj
    cfv
    #
    @4
    cdiv
    co
    #
    cc
    wcel
    @17
    cabs
    cfv
    #
    c1
    wceq
    #
    @4
    @17
    cA
    cmul
    co
    #
    wceq
    #
    @8
    @15
    @16
    @4
    @15
    cA
    @0
    @14
    simpl
    #
    cjcld
    #
    @15
    @4
    @0
    @4
    cr
    wcel
    @14
    cA
    abscl
    adantr
    recnd
    #
    @0
    @4
    cc0
    wne
    #
    @14
    @0
    @4
    cc0
    cA
    cc0
    cA
    abs00
    necon3bid
    biimpar
    #
    divcld
    #
    @15
    @18
    @16
    cabs
    cfv
    #
    @4
    cabs
    cfv
    #
    cdiv
    co
    #
    @4
    @4
    cdiv
    co
    c1
    @15
    @16
    cc
    wcel
    @4
    cc
    wcel
    @25
    @18
    @30
    wceq
    @23
    @24
    @26
    @16
    @4
    absdiv
    syl3anc
    @15
    @28
    @4
    @29
    @4
    cdiv
    @0
    @28
    @4
    wceq
    @14
    cA
    abscj
    adantr
    @0
    @29
    @4
    wceq
    @14
    cA
    absidm
    adantr
    oveq12d
    @15
    @4
    @24
    @26
    dividd
    3eqtrd
    @15
    cA
    @16
    cmul
    co
    #
    @4
    cdiv
    co
    cA
    @17
    cmul
    co
    @4
    @20
    @15
    cA
    @16
    @4
    @22
    @23
    @24
    @26
    divassd
    @15
    @4
    @4
    @31
    @24
    @24
    @26
    @15
    @4
    c2
    cexp
    co
    #
    @4
    @4
    cmul
    co
    @31
    @15
    @4
    @24
    sqvald
    @0
    @32
    @31
    wceq
    @14
    cA
    absvalsq
    adantr
    eqtr3d
    mvllmuld
    @15
    @17
    cA
    @27
    @22
    mulcomd
    3eqtr4d
    @7
    @19
    @21
    wa
    vx
    @17
    cc
    @1
    @17
    wceq
    #
    @3
    @19
    @6
    @21
    @33
    @2
    @18
    c1
    @1
    @17
    cabs
    fveq2
    eqeq1d
    @33
    @5
    @20
    @4
    @1
    @17
    cA
    cmul
    oveq1
    eqeq2d
    anbi12d
    rspcev
    syl12anc
    @12
    @0
    ci
    cc
    wcel
    ci
    cabs
    cfv
    #
    c1
    wceq
    #
    cc0
    ci
    cc0
    cmul
    co
    #
    wceq
    #
    wa
    #
    @12
    ax-icn
    @35
    @37
    absi
    @36
    cc0
    it0e0
    eqcomi
    pm3.2i
    @11
    @38
    vx
    ci
    cc
    @1
    ci
    wceq
    #
    @3
    @35
    @10
    @37
    @39
    @2
    @34
    c1
    @1
    ci
    cabs
    fveq2
    eqeq1d
    @39
    @9
    @36
    cc0
    @1
    ci
    cc0
    cmul
    oveq1
    eqeq2d
    anbi12d
    rspcev
    mp2an
    a1i
    pm2.61ne
end
