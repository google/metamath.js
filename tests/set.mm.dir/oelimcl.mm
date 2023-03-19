include "con0.mm"
include "c2o.mm"
include "cdif.mm"
include "wcel.mm"
include "wlim.mm"
include "wa.mm"
include "coe.mm"
include "co.mm"
include "word.mm"
include "c0.mm"
include "cv.mm"
include "csuc.mm"
include "wral.mm"
include "eldifi.mm"
include "limelon.mm"
include "oecl.mm"
include "syl2an.mm"
include "eloni.mm"
include "syl.mm"
include "adantr.mm"
include "adantl.mm"
include "dif20el.mm"
include "oen0.mm"
include "syl21anc.mm"
include "c1o.mm"
include "ciun.mm"
include "wceq.mm"
include "oelim2.mm"
include "sylan.mm"
include "eleq2d.mm"
include "wrex.mm"
include "eliun.mm"
include "wi.mm"
include "wss.mm"
include "simprl.mm"
include "onelon.mm"
include "syl2anc.mm"
include "simprr.mm"
include "ordsucss.mm"
include "sylc.mm"
include "simpll.mm"
include "oeordi.mm"
include "mpd.mm"
include "suceloni.mm"
include "ontr2.mm"
include "mp2and.mm"
include "expr.mm"
include "sylan2.mm"
include "rexlimdva.mm"
include "syl5bi.mm"
include "sylbid.mm"
include "ralrimiv.mm"
include "dflim4.mm"
include "syl3anbrc.mm"

theorem oelimcl
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. ( On \ 2o ) /\ ( B e. C /\ Lim B ) ) -> Lim ( A ^o B ) )

  proof
    cA
    con0
    c2o
    cdif
    wcel
    #
    cB
    cC
    wcel
    cB
    wlim
    wa
    #
    wa
    #
    cA
    cB
    coe
    co
    #
    word
    #
    c0
    @3
    wcel
    #
    vx
    cv
    #
    csuc
    #
    @3
    wcel
    #
    vx
    @3
    wral
    @3
    wlim
    @2
    @3
    con0
    wcel
    #
    @4
    @0
    cA
    con0
    wcel
    #
    cB
    con0
    wcel
    #
    @9
    @1
    cA
    con0
    c2o
    eldifi
    #
    cB
    cC
    limelon
    #
    cA
    cB
    oecl
    syl2an
    #
    @3
    eloni
    syl
    @2
    @10
    @11
    c0
    cA
    wcel
    #
    @5
    @0
    @10
    @1
    @12
    adantr
    #
    @1
    @11
    @0
    @13
    adantl
    #
    @0
    @15
    @1
    cA
    dif20el
    adantr
    cA
    cB
    oen0
    syl21anc
    @2
    @8
    vx
    @3
    @2
    @6
    @3
    wcel
    @6
    vy
    cB
    c1o
    cdif
    #
    cA
    vy
    cv
    #
    coe
    co
    #
    ciun
    #
    wcel
    #
    @8
    @2
    @3
    @21
    @6
    @0
    @10
    @1
    @3
    @21
    wceq
    @12
    vy
    cA
    cB
    cC
    oelim2
    sylan
    eleq2d
    @22
    @6
    @20
    wcel
    #
    vy
    @18
    wrex
    @2
    @8
    vy
    @6
    @18
    @20
    eliun
    @2
    @23
    @8
    vy
    @18
    @19
    @18
    wcel
    @2
    @19
    cB
    wcel
    #
    @23
    @8
    wi
    @19
    cB
    c1o
    eldifi
    @2
    @24
    @23
    @8
    @2
    @24
    @23
    wa
    #
    wa
    #
    @7
    @20
    wss
    #
    @20
    @3
    wcel
    #
    @8
    @26
    @20
    word
    #
    @23
    @27
    @26
    @20
    con0
    wcel
    #
    @29
    @26
    @10
    @19
    con0
    wcel
    #
    @30
    @2
    @10
    @25
    @16
    adantr
    @26
    @11
    @24
    @31
    @2
    @11
    @25
    @17
    adantr
    #
    @2
    @24
    @23
    simprl
    #
    cB
    @19
    onelon
    syl2anc
    cA
    @19
    oecl
    syl2anc
    #
    @20
    eloni
    syl
    @2
    @24
    @23
    simprr
    #
    @6
    @20
    ordsucss
    sylc
    @26
    @24
    @28
    @33
    @26
    @11
    @0
    @24
    @28
    wi
    @32
    @0
    @1
    @25
    simpll
    @19
    cB
    cA
    oeordi
    syl2anc
    mpd
    @26
    @7
    con0
    wcel
    #
    @9
    @27
    @28
    wa
    @8
    wi
    @26
    @6
    con0
    wcel
    #
    @36
    @26
    @30
    @23
    @37
    @34
    @35
    @20
    @6
    onelon
    syl2anc
    @6
    suceloni
    syl
    @2
    @9
    @25
    @14
    adantr
    @7
    @20
    @3
    ontr2
    syl2anc
    mp2and
    expr
    sylan2
    rexlimdva
    syl5bi
    sylbid
    ralrimiv
    vx
    @3
    dflim4
    syl3anbrc
end
