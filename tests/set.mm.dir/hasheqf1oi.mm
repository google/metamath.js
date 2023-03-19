include "cfn.mm"
include "wcel.mm"
include "cv.mm"
include "wf1o.mm"
include "wex.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wa.mm"
include "hasheqf1o.mm"
include "biimprd.mm"
include "a1d.mm"
include "wn.mm"
include "fiinfnf1o.mm"
include "pm2.21d.mm"
include "19.41v.mm"
include "ccnv.mm"
include "wrel.mm"
include "wb.mm"
include "f1orel.mm"
include "adantr.mm"
include "f1ocnvb.mm"
include "syl.mm"
include "cvv.mm"
include "wf.mm"
include "f1of.mm"
include "fex.mm"
include "sylan.mm"
include "cnvexg.mm"
include "f1oeq1.mm"
include "spcegv.mm"
include "3syl.mm"
include "pm2.24.mm"
include "syl6.mm"
include "sylbid.mm"
include "com12.mm"
include "anabsi5.mm"
include "exlimiv.mm"
include "sylbir.mm"
include "ex.mm"
include "com13.mm"
include "ancoms.mm"
include "cpnf.mm"
include "hashinf.mm"
include "expcom.mm"
include "imp.mm"
include "wfo.mm"
include "simpr.mm"
include "f1ofo.mm"
include "focdmex.mm"
include "syl2an.mm"
include "ad3antlr.mm"
include "mpd.mm"
include "eqtr4d.mm"
include "exlimdv.mm"
include "4cases.mm"

theorem hasheqf1oi
  let cA: class A
  let cB: class B
  let vf: setvar f
  let cV: class V
  let vg: setvar g

  disjoint A f
  disjoint B f
  disjoint V f
  disjoint A g
  disjoint f g
  disjoint B g
  assert |- ( A e. V -> ( E. f f : A -1-1-onto-> B -> ( # ` A ) = ( # ` B ) ) )

  proof
    cA
    cfn
    wcel
    #
    cB
    cfn
    wcel
    #
    cA
    cV
    wcel
    #
    cA
    cB
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    #
    cA
    chash
    cfv
    #
    cB
    chash
    cfv
    #
    wceq
    #
    wi
    #
    wi
    #
    @0
    @1
    wa
    #
    @9
    @2
    @11
    @8
    @5
    cA
    cB
    vf
    hasheqf1o
    biimprd
    a1d
    @0
    @1
    wn
    #
    wa
    #
    @9
    @2
    @13
    @5
    @8
    cA
    cB
    vf
    fiinfnf1o
    pm2.21d
    a1d
    @1
    @0
    wn
    #
    @10
    @1
    @14
    wa
    cB
    cA
    vg
    cv
    #
    wf1o
    #
    vg
    wex
    #
    wn
    #
    @10
    cB
    cA
    vg
    fiinfnf1o
    @5
    @2
    @18
    @8
    @5
    @2
    @18
    @8
    wi
    #
    @5
    @2
    wa
    @4
    @2
    wa
    #
    vf
    wex
    @19
    @4
    @2
    vf
    19.41v
    @20
    @19
    vf
    @4
    @2
    @19
    @20
    @4
    @19
    @20
    @4
    cB
    cA
    @3
    ccnv
    #
    wf1o
    #
    @19
    @20
    @3
    wrel
    #
    @4
    @22
    wb
    @4
    @23
    @2
    cA
    cB
    @3
    f1orel
    adantr
    cA
    cB
    @3
    f1ocnvb
    syl
    @20
    @22
    @17
    @19
    @20
    @3
    cvv
    wcel
    #
    @21
    cvv
    wcel
    @22
    @17
    wi
    @4
    cA
    cB
    @3
    wf
    @2
    @24
    cA
    cB
    @3
    f1of
    cA
    cB
    cV
    @3
    fex
    sylan
    @3
    cvv
    cnvexg
    @16
    @22
    vg
    @21
    cvv
    cB
    cA
    @15
    @21
    f1oeq1
    spcegv
    3syl
    @17
    @8
    pm2.24
    syl6
    sylbid
    com12
    anabsi5
    exlimiv
    sylbir
    ex
    com13
    syl
    ancoms
    @14
    @12
    wa
    #
    @2
    @9
    @25
    @2
    wa
    #
    @4
    @8
    vf
    @26
    @4
    @8
    @26
    @4
    wa
    #
    @6
    cpnf
    @7
    @26
    @6
    cpnf
    wceq
    #
    @4
    @25
    @2
    @28
    @14
    @2
    @28
    wi
    @12
    @2
    @14
    @28
    cA
    cV
    hashinf
    expcom
    adantr
    imp
    adantr
    @27
    cB
    cvv
    wcel
    #
    @7
    cpnf
    wceq
    #
    @26
    @2
    cA
    cB
    @3
    wfo
    @29
    @4
    @25
    @2
    simpr
    cA
    cB
    @3
    f1ofo
    cA
    cB
    @3
    cV
    focdmex
    syl2an
    @12
    @29
    @30
    wi
    @14
    @2
    @4
    @29
    @12
    @30
    cB
    cvv
    hashinf
    expcom
    ad3antlr
    mpd
    eqtr4d
    ex
    exlimdv
    ex
    4cases
end
