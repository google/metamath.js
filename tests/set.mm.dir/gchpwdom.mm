include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cgch.mm"
include "wcel.mm"
include "w3a.mm"
include "csdm.mm"
include "cpw.mm"
include "wa.mm"
include "ccda.mm"
include "co.mm"
include "cen.mm"
include "cvv.mm"
include "simpl2.mm"
include "pwexg.mm"
include "syl.mm"
include "simpl3.mm"
include "cdadom3.mm"
include "syl2anc.mm"
include "domen2.mm"
include "syl5ibrcom.mm"
include "cdacomen.mm"
include "entr.mm"
include "mpan.mm"
include "ensym.mm"
include "endom.mm"
include "3syl.mm"
include "wb.mm"
include "cfn.mm"
include "wn.mm"
include "domsdomtr.mm"
include "3ad2antl1.mm"
include "sdomnsym.mm"
include "isfinite.mm"
include "sylnibr.mm"
include "gchcdaidm.mm"
include "pwen.mm"
include "domen1.mm"
include "pwcdadom.mm"
include "wi.mm"
include "canth2g.mm"
include "sdomdomtr.mm"
include "ex.mm"
include "gchi.mm"
include "3expia.mm"
include "3ad2antl2.mm"
include "simpl1.mm"
include "domnsym.mm"
include "pm2.21d.mm"
include "syl5bi.mm"
include "3syld.mm"
include "syl5.mm"
include "sylbird.mm"
include "wo.mm"
include "domentr.mm"
include "sylancl.mm"
include "sdomdom.mm"
include "adantl.mm"
include "pwdom.mm"
include "cdadom1.mm"
include "cdadom2.mm"
include "domtr.mm"
include "c1o.mm"
include "pwcda1.mm"
include "gchcda1.mm"
include "gchor.mm"
include "syl22anc.mm"
include "mpjaod.mm"
include "reldom.mm"
include "brrelexi.mm"
include "pwexb.mm"
include "sylbir.mm"
include "mpancom.mm"
include "impbid1.mm"

theorem gchpwdom
  let cA: class A
  let cB: class B


  assert |- ( ( _om ~<_ A /\ A e. GCH /\ B e. GCH ) -> ( A ~< B <-> ~P A ~<_ B ) )

  proof
    com
    cA
    cdom
    wbr
    #
    cA
    cgch
    wcel
    #
    cB
    cgch
    wcel
    #
    w3a
    #
    cA
    cB
    csdm
    wbr
    #
    cA
    cpw
    #
    cB
    cdom
    wbr
    #
    @3
    @4
    @6
    @3
    @4
    wa
    #
    cB
    @5
    cB
    ccda
    co
    #
    cen
    wbr
    #
    @6
    @8
    cB
    cpw
    #
    cen
    wbr
    #
    @7
    @6
    @9
    @5
    @8
    cdom
    wbr
    #
    @7
    @5
    cvv
    wcel
    #
    @2
    @12
    @7
    @1
    @13
    @0
    @1
    @2
    @4
    simpl2
    cA
    cgch
    pwexg
    syl
    #
    @0
    @1
    @2
    @4
    simpl3
    #
    @5
    cB
    cvv
    cgch
    cdadom3
    syl2anc
    cB
    @8
    @5
    domen2
    syl5ibrcom
    @11
    @10
    cB
    @5
    ccda
    co
    #
    cdom
    wbr
    #
    @7
    @6
    @11
    @16
    @10
    cen
    wbr
    #
    @10
    @16
    cen
    wbr
    @17
    @16
    @8
    cen
    wbr
    #
    @11
    @18
    cB
    @5
    cdacomen
    #
    @16
    @8
    @10
    entr
    mpan
    @16
    @10
    ensym
    @10
    @16
    endom
    3syl
    @7
    @17
    cB
    cB
    ccda
    co
    #
    cpw
    #
    @16
    cdom
    wbr
    #
    @6
    @7
    @21
    cB
    cen
    wbr
    #
    @22
    @10
    cen
    wbr
    @23
    @17
    wb
    @7
    @2
    cB
    cfn
    wcel
    #
    wn
    #
    @24
    @15
    @7
    cB
    com
    csdm
    wbr
    #
    @25
    @7
    com
    cB
    csdm
    wbr
    #
    @27
    wn
    @0
    @1
    @4
    @28
    @2
    com
    cA
    cB
    domsdomtr
    3ad2antl1
    com
    cB
    sdomnsym
    syl
    cB
    isfinite
    sylnibr
    #
    cB
    gchcdaidm
    syl2anc
    @21
    cB
    pwen
    @22
    @10
    @16
    domen1
    3syl
    @23
    @10
    @5
    cdom
    wbr
    #
    @7
    @6
    cB
    @5
    pwcdadom
    @7
    @30
    cB
    @5
    csdm
    wbr
    #
    cA
    cfn
    wcel
    #
    @6
    @7
    @2
    cB
    @10
    csdm
    wbr
    #
    @30
    @31
    wi
    @15
    cB
    cgch
    canth2g
    #
    @33
    @30
    @31
    cB
    @10
    @5
    sdomdomtr
    ex
    3syl
    @1
    @0
    @4
    @31
    @32
    wi
    @2
    @1
    @4
    @31
    @32
    cA
    cB
    gchi
    3expia
    3ad2antl2
    @32
    cA
    com
    csdm
    wbr
    #
    @7
    @6
    cA
    isfinite
    @7
    @35
    @6
    @7
    @0
    @35
    wn
    @0
    @1
    @2
    @4
    simpl1
    com
    cA
    domnsym
    syl
    pm2.21d
    syl5bi
    3syld
    syl5
    sylbird
    syl5
    @7
    @2
    @26
    cB
    @8
    cdom
    wbr
    #
    @8
    @10
    cdom
    wbr
    #
    @9
    @11
    wo
    @15
    @29
    @7
    cB
    @16
    cdom
    wbr
    #
    @19
    @36
    @7
    @2
    @13
    @38
    @15
    @14
    cB
    @5
    cgch
    cvv
    cdadom3
    syl2anc
    @20
    cB
    @16
    @8
    domentr
    sylancl
    @7
    @8
    @10
    @10
    ccda
    co
    #
    cdom
    wbr
    #
    @39
    @10
    cen
    wbr
    #
    @37
    @7
    @8
    @10
    cB
    ccda
    co
    #
    cdom
    wbr
    #
    @42
    @39
    cdom
    wbr
    #
    @40
    @7
    cA
    cB
    cdom
    wbr
    #
    @5
    @10
    cdom
    wbr
    @43
    @4
    @45
    @3
    cA
    cB
    sdomdom
    adantl
    cA
    cB
    pwdom
    @5
    @10
    cB
    cdadom1
    3syl
    @7
    @33
    cB
    @10
    cdom
    wbr
    @44
    @7
    @2
    @33
    @15
    @34
    syl
    cB
    @10
    sdomdom
    cB
    @10
    @10
    cdadom2
    3syl
    @8
    @42
    @39
    domtr
    syl2anc
    @7
    @39
    cB
    c1o
    ccda
    co
    #
    cpw
    #
    cen
    wbr
    #
    @47
    @10
    cen
    wbr
    #
    @41
    @7
    @2
    @48
    @15
    cB
    cgch
    pwcda1
    syl
    @7
    @46
    cB
    cen
    wbr
    #
    @49
    @7
    @2
    @26
    @50
    @15
    @29
    cB
    gchcda1
    syl2anc
    @46
    cB
    pwen
    syl
    @39
    @47
    @10
    entr
    syl2anc
    @8
    @39
    @10
    domentr
    syl2anc
    cB
    @8
    gchor
    syl22anc
    mpjaod
    ex
    cA
    @5
    csdm
    wbr
    #
    @6
    @4
    @6
    @13
    @51
    @5
    cB
    cdom
    reldom
    brrelexi
    @13
    cA
    cvv
    wcel
    @51
    cA
    pwexb
    cA
    cvv
    canth2g
    sylbir
    syl
    cA
    @5
    cB
    sdomdomtr
    mpancom
    impbid1
end
