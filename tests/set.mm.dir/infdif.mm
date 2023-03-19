include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "csdm.mm"
include "w3a.mm"
include "cdif.mm"
include "cen.mm"
include "wss.mm"
include "simp1.mm"
include "difss.mm"
include "ssdomg.mm"
include "mpisyl.mm"
include "ccda.mm"
include "co.mm"
include "cun.mm"
include "sdomdom.mm"
include "3ad2ant3.mm"
include "numdom.mm"
include "syl2anc.mm"
include "unnum.mm"
include "ssun1.mm"
include "undif1.mm"
include "ssnum.mm"
include "sylancl.mm"
include "uncdadom.mm"
include "syl5eqbrr.mm"
include "domtr.mm"
include "wn.mm"
include "simp3.mm"
include "cdadom1.mm"
include "syl.mm"
include "wi.mm"
include "ex.mm"
include "simp2.mm"
include "cdainf.mm"
include "biimpri.mm"
include "domrefg.mm"
include "infcdaabs.mm"
include "3com23.mm"
include "3expia.mm"
include "mpdan.mm"
include "syl2im.mm"
include "syld.mm"
include "domen2.mm"
include "biimpcd.mm"
include "sylcom.mm"
include "domnsym.mm"
include "syl56.mm"
include "mt2d.mm"
include "wb.mm"
include "domtri2.mm"
include "mpbird.mm"
include "cdadom2.mm"
include "sylibr.mm"
include "syl3anc.mm"
include "domentr.mm"
include "sbth.mm"

theorem infdif
  let cA: class A
  let cB: class B


  assert |- ( ( A e. dom card /\ _om ~<_ A /\ B ~< A ) -> ( A \ B ) ~~ A )

  proof
    cA
    ccrd
    cdm
    #
    wcel
    #
    com
    cA
    cdom
    wbr
    #
    cB
    cA
    csdm
    wbr
    #
    w3a
    #
    cA
    cB
    cdif
    #
    cA
    cdom
    wbr
    #
    cA
    @5
    cdom
    wbr
    #
    @5
    cA
    cen
    wbr
    @4
    @1
    @5
    cA
    wss
    #
    @6
    @1
    @2
    @3
    simp1
    #
    cA
    cB
    difss
    #
    @5
    cA
    @0
    ssdomg
    mpisyl
    @4
    cA
    @5
    @5
    ccda
    co
    #
    cdom
    wbr
    #
    @11
    @5
    cen
    wbr
    #
    @7
    @4
    cA
    @5
    cB
    ccda
    co
    #
    cdom
    wbr
    #
    @14
    @11
    cdom
    wbr
    #
    @12
    @4
    cA
    cA
    cB
    cun
    #
    cdom
    wbr
    #
    @17
    @14
    cdom
    wbr
    @15
    @4
    @17
    @0
    wcel
    #
    cA
    @17
    wss
    @18
    @4
    @1
    cB
    @0
    wcel
    #
    @19
    @9
    @4
    @1
    cB
    cA
    cdom
    wbr
    #
    @20
    @9
    @3
    @1
    @21
    @2
    cB
    cA
    sdomdom
    3ad2ant3
    cA
    cB
    numdom
    syl2anc
    #
    cA
    cB
    unnum
    syl2anc
    cA
    cB
    ssun1
    cA
    @17
    @0
    ssdomg
    mpisyl
    @4
    @17
    @5
    cB
    cun
    #
    @14
    cdom
    cA
    cB
    undif1
    @4
    @5
    @0
    wcel
    #
    @20
    @23
    @14
    cdom
    wbr
    @4
    @1
    @8
    @24
    @9
    @10
    cA
    @5
    ssnum
    sylancl
    #
    @22
    @5
    cB
    @0
    @0
    uncdadom
    syl2anc
    syl5eqbrr
    cA
    @17
    @14
    domtr
    syl2anc
    #
    @4
    cB
    @5
    cdom
    wbr
    #
    @16
    @4
    @27
    @5
    cB
    csdm
    wbr
    #
    wn
    #
    @4
    @28
    @3
    @1
    @2
    @3
    simp3
    @28
    @14
    cB
    cB
    ccda
    co
    #
    cdom
    wbr
    #
    @4
    cA
    cB
    cdom
    wbr
    #
    @3
    wn
    @28
    @5
    cB
    cdom
    wbr
    @31
    @5
    cB
    sdomdom
    @5
    cB
    cB
    cdadom1
    syl
    @4
    @31
    cA
    @30
    cdom
    wbr
    #
    @32
    @4
    @15
    @31
    @33
    wi
    @26
    @15
    @31
    @33
    cA
    @14
    @30
    domtr
    ex
    syl
    @4
    @33
    @30
    cB
    cen
    wbr
    #
    @32
    @4
    @33
    com
    @30
    cdom
    wbr
    #
    @34
    @4
    @2
    @33
    @35
    wi
    @1
    @2
    @3
    simp2
    #
    @2
    @33
    @35
    com
    cA
    @30
    domtr
    ex
    syl
    @4
    @20
    @35
    com
    cB
    cdom
    wbr
    #
    @34
    @22
    @37
    @35
    cB
    cdainf
    biimpri
    @20
    cB
    cB
    cdom
    wbr
    #
    @37
    @34
    wi
    cB
    @0
    domrefg
    @20
    @38
    @37
    @34
    @20
    @37
    @38
    @34
    cB
    cB
    infcdaabs
    3com23
    3expia
    mpdan
    syl2im
    syld
    @34
    @33
    @32
    @30
    cB
    cA
    domen2
    biimpcd
    sylcom
    syld
    cA
    cB
    domnsym
    syl56
    mt2d
    @4
    @20
    @24
    @27
    @29
    wb
    @22
    @25
    cB
    @5
    domtri2
    syl2anc
    mpbird
    cB
    @5
    @5
    cdadom2
    syl
    cA
    @14
    @11
    domtr
    syl2anc
    #
    @4
    @24
    com
    @5
    cdom
    wbr
    #
    @5
    @5
    cdom
    wbr
    #
    @13
    @25
    @4
    com
    @11
    cdom
    wbr
    #
    @40
    @4
    @2
    @12
    @42
    @36
    @39
    com
    cA
    @11
    domtr
    syl2anc
    @5
    cdainf
    sylibr
    @4
    @24
    @41
    @25
    @5
    @0
    domrefg
    syl
    @5
    @5
    infcdaabs
    syl3anc
    cA
    @11
    @5
    domentr
    syl2anc
    @5
    cA
    sbth
    syl2anc
end
