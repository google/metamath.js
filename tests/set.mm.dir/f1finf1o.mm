include "cen.mm"
include "wbr.mm"
include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "wf1.mm"
include "wf1o.mm"
include "wfo.mm"
include "simpr.mm"
include "wfn.mm"
include "crn.mm"
include "wceq.mm"
include "wf.mm"
include "f1f.mm"
include "adantl.mm"
include "ffn.mm"
include "syl.mm"
include "simpll.mm"
include "wne.mm"
include "wpss.mm"
include "wn.mm"
include "wss.mm"
include "wb.mm"
include "frn.mm"
include "df-pss.mm"
include "baib.mm"
include "csdm.mm"
include "cmap.mm"
include "co.mm"
include "cvv.mm"
include "simplr.mm"
include "relen.mm"
include "brrelexi.mm"
include "elmapd.mm"
include "mpbird.mm"
include "f1f1orn.mm"
include "f1oen3g.mm"
include "syl2anc.mm"
include "wi.mm"
include "php3.mm"
include "ex.mm"
include "ensdomtr.mm"
include "syl6an.mm"
include "sdomnen.mm"
include "syl6.mm"
include "sylbird.mm"
include "necon4ad.mm"
include "mpd.mm"
include "df-fo.mm"
include "sylanbrc.mm"
include "df-f1o.mm"
include "f1of1.mm"
include "impbid1.mm"

theorem f1finf1o
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( ( A ~~ B /\ B e. Fin ) -> ( F : A -1-1-> B <-> F : A -1-1-onto-> B ) )

  proof
    cA
    cB
    cen
    wbr
    #
    cB
    cfn
    wcel
    #
    wa
    #
    cA
    cB
    cF
    wf1
    #
    cA
    cB
    cF
    wf1o
    #
    @2
    @3
    @4
    @2
    @3
    wa
    #
    @3
    cA
    cB
    cF
    wfo
    #
    @4
    @2
    @3
    simpr
    @5
    cF
    cA
    wfn
    #
    cF
    crn
    #
    cB
    wceq
    #
    @6
    @5
    cA
    cB
    cF
    wf
    #
    @7
    @3
    @10
    @2
    cA
    cB
    cF
    f1f
    adantl
    #
    cA
    cB
    cF
    ffn
    syl
    @5
    @0
    @9
    @0
    @1
    @3
    simpll
    #
    @5
    @0
    @8
    cB
    @5
    @8
    cB
    wne
    #
    @8
    cB
    wpss
    #
    @0
    wn
    #
    @5
    @8
    cB
    wss
    #
    @14
    @13
    wb
    @5
    @10
    @16
    @11
    cA
    cB
    cF
    frn
    syl
    @14
    @16
    @13
    @8
    cB
    df-pss
    baib
    syl
    @5
    @14
    cA
    cB
    csdm
    wbr
    #
    @15
    @5
    cA
    @8
    cen
    wbr
    #
    @14
    @8
    cB
    csdm
    wbr
    #
    @17
    @5
    cF
    cB
    cA
    cmap
    co
    #
    wcel
    #
    cA
    @8
    cF
    wf1o
    #
    @18
    @5
    @21
    @10
    @11
    @5
    cB
    cA
    cF
    cfn
    cvv
    @0
    @1
    @3
    simplr
    #
    @5
    @0
    cA
    cvv
    wcel
    @12
    cA
    cB
    cen
    relen
    brrelexi
    syl
    elmapd
    mpbird
    @3
    @22
    @2
    cA
    cB
    cF
    f1f1orn
    adantl
    cA
    @8
    cF
    @20
    f1oen3g
    syl2anc
    @5
    @1
    @14
    @19
    wi
    @23
    @1
    @14
    @19
    cB
    @8
    php3
    ex
    syl
    cA
    @8
    cB
    ensdomtr
    syl6an
    cA
    cB
    sdomnen
    syl6
    sylbird
    necon4ad
    mpd
    cA
    cB
    cF
    df-fo
    sylanbrc
    cA
    cB
    cF
    df-f1o
    sylanbrc
    ex
    cA
    cB
    cF
    f1of1
    impbid1
end
