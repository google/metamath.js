include "csur.mm"
include "wcel.mm"
include "con0.mm"
include "wa.mm"
include "cdm.mm"
include "cdif.mm"
include "csn.mm"
include "cxp.mm"
include "cun.mm"
include "wfun.mm"
include "crn.mm"
include "c1o.mm"
include "c2o.mm"
include "cpr.mm"
include "wss.mm"
include "nofun.mm"
include "wfn.mm"
include "fnconstg.mm"
include "fnfun.mm"
include "mp2b.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wne.mm"
include "snnzg.mm"
include "dmxp.mm"
include "ineq2i.mm"
include "disjdif.mm"
include "eqtri.mm"
include "funun.mm"
include "mpan2.mm"
include "syl.mm"
include "adantr.mm"
include "dmun.mm"
include "uneq2i.mm"
include "nodmon.mm"
include "undif.mm"
include "wi.mm"
include "eleq1a.mm"
include "adantl.mm"
include "syl5bi.mm"
include "ssdif0.mm"
include "uneq2.mm"
include "un0.mm"
include "syl6eq.mm"
include "eleq1d.mm"
include "biimprcd.mm"
include "word.mm"
include "wo.mm"
include "eloni.mm"
include "ordtri2or2.mm"
include "syl2an.mm"
include "mpjaod.mm"
include "sylan.mm"
include "syl5eqel.mm"
include "rnun.mm"
include "norn.mm"
include "rnxpss.mm"
include "snssi.mm"
include "ax-mp.mm"
include "sstri.mm"
include "unss.mm"
include "sylanblc.mm"
include "syl5eqss.mm"
include "elno2.mm"
include "syl3anbrc.mm"

theorem noextendseq
  let cA: class A
  let cB: class B
  let cX: class X
  assume noextend.1: |- X e. { 1o , 2o }


  assert |- ( ( A e. No /\ B e. On ) -> ( A u. ( ( B \ dom A ) X. { X } ) ) e. No )

  proof
    cA
    csur
    wcel
    #
    cB
    con0
    wcel
    #
    wa
    #
    cA
    cB
    cA
    cdm
    #
    cdif
    #
    cX
    csn
    #
    cxp
    #
    cun
    #
    wfun
    #
    @7
    cdm
    #
    con0
    wcel
    @7
    crn
    #
    c1o
    c2o
    cpr
    #
    wss
    @7
    csur
    wcel
    @0
    @8
    @1
    @0
    cA
    wfun
    #
    @8
    cA
    nofun
    @12
    @6
    wfun
    #
    @8
    cX
    @11
    wcel
    #
    @6
    @4
    wfn
    @13
    noextend.1
    @4
    cX
    @11
    fnconstg
    @4
    @6
    fnfun
    mp2b
    @12
    @13
    wa
    @3
    @6
    cdm
    #
    cin
    #
    c0
    wceq
    @8
    @16
    @3
    @4
    cin
    c0
    @15
    @4
    @3
    @14
    @5
    c0
    wne
    @15
    @4
    wceq
    noextend.1
    cX
    @11
    snnzg
    @4
    @5
    dmxp
    mp2b
    #
    ineq2i
    @3
    cB
    disjdif
    eqtri
    cA
    @6
    funun
    mpan2
    mpan2
    syl
    adantr
    @2
    @9
    @3
    @4
    cun
    #
    con0
    @9
    @3
    @15
    cun
    @18
    cA
    @6
    dmun
    @15
    @4
    @3
    @17
    uneq2i
    eqtri
    @0
    @3
    con0
    wcel
    #
    @1
    @18
    con0
    wcel
    #
    cA
    nodmon
    @19
    @1
    wa
    #
    @3
    cB
    wss
    #
    @20
    cB
    @3
    wss
    #
    @22
    @18
    cB
    wceq
    #
    @21
    @20
    @3
    cB
    undif
    @1
    @24
    @20
    wi
    @19
    cB
    con0
    @18
    eleq1a
    adantl
    syl5bi
    @23
    @4
    c0
    wceq
    #
    @21
    @20
    cB
    @3
    ssdif0
    @19
    @25
    @20
    wi
    @1
    @25
    @20
    @19
    @25
    @18
    @3
    con0
    @25
    @18
    @3
    c0
    cun
    @3
    @4
    c0
    @3
    uneq2
    @3
    un0
    syl6eq
    eleq1d
    biimprcd
    adantr
    syl5bi
    @19
    @3
    word
    cB
    word
    @22
    @23
    wo
    @1
    @3
    eloni
    cB
    eloni
    @3
    cB
    ordtri2or2
    syl2an
    mpjaod
    sylan
    syl5eqel
    @2
    @10
    cA
    crn
    #
    @6
    crn
    #
    cun
    #
    @11
    cA
    @6
    rnun
    @2
    @26
    @11
    wss
    #
    @27
    @11
    wss
    @28
    @11
    wss
    @0
    @29
    @1
    cA
    norn
    adantr
    @27
    @5
    @11
    @4
    @5
    rnxpss
    @14
    @5
    @11
    wss
    noextend.1
    cX
    @11
    snssi
    ax-mp
    sstri
    @26
    @27
    @11
    unss
    sylanblc
    syl5eqss
    @7
    elno2
    syl3anbrc
end
