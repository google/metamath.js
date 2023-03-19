include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wf1o.mm"
include "wex.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
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
include "simprl.mm"
include "simprr.mm"
include "fex2.mm"
include "syl3anc.mm"
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
include "impcom.mm"
include "adantl.mm"
include "eqtr4d.mm"
include "4cases.mm"

theorem hasheqf1oiOLD
  let cA: class A
  let cB: class B
  let vf: setvar f
  let cV: class V
  let cW: class W
  let vg: setvar g

  disjoint A f
  disjoint B f
  disjoint V f
  disjoint W f
  disjoint A g
  disjoint f g
  disjoint B g
  assert |- ( ( A e. V /\ B e. W ) -> ( E. f f : A -1-1-onto-> B -> ( # ` A ) = ( # ` B ) ) )

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
    cB
    cW
    wcel
    #
    wa
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
    @11
    @4
    @13
    @10
    @7
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
    @11
    @4
    @15
    @7
    @10
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
    @12
    @1
    @16
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
    @12
    cB
    cA
    vg
    fiinfnf1o
    @7
    @4
    @20
    @10
    @7
    @4
    @20
    @10
    wi
    #
    @7
    @4
    wa
    @6
    @4
    wa
    #
    vf
    wex
    @21
    @6
    @4
    vf
    19.41v
    @22
    @21
    vf
    @6
    @4
    @21
    @22
    @6
    @21
    @22
    @6
    cB
    cA
    @5
    ccnv
    #
    wf1o
    #
    @21
    @22
    @5
    wrel
    #
    @6
    @24
    wb
    @6
    @25
    @4
    cA
    cB
    @5
    f1orel
    adantr
    cA
    cB
    @5
    f1ocnvb
    syl
    @22
    @24
    @19
    @21
    @22
    @5
    cvv
    wcel
    #
    @23
    cvv
    wcel
    @24
    @19
    wi
    @22
    cA
    cB
    @5
    wf
    #
    @2
    @3
    @26
    @6
    @27
    @4
    cA
    cB
    @5
    f1of
    adantr
    @6
    @2
    @3
    simprl
    @6
    @2
    @3
    simprr
    cA
    cB
    @5
    cV
    cW
    fex2
    syl3anc
    @5
    cvv
    cnvexg
    @18
    @24
    vg
    @23
    cvv
    cB
    cA
    @17
    @23
    f1oeq1
    spcegv
    3syl
    @19
    @10
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
    @16
    @14
    wa
    #
    @4
    @11
    @28
    @4
    wa
    #
    @10
    @7
    @29
    @8
    cpnf
    @9
    @4
    @28
    @8
    cpnf
    wceq
    #
    @2
    @28
    @30
    wi
    @3
    @28
    @2
    @30
    @16
    @2
    @30
    wi
    @14
    @2
    @16
    @30
    cA
    cV
    hashinf
    expcom
    adantr
    com12
    adantr
    impcom
    @4
    @28
    @9
    cpnf
    wceq
    #
    @3
    @28
    @31
    wi
    @2
    @28
    @3
    @31
    @14
    @3
    @31
    wi
    @16
    @3
    @14
    @31
    cB
    cW
    hashinf
    expcom
    adantl
    com12
    adantl
    impcom
    eqtr4d
    a1d
    ex
    4cases
end
