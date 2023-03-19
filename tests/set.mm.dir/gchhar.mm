include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cgch.mm"
include "wcel.mm"
include "cpw.mm"
include "w3a.mm"
include "char.mm"
include "cfv.mm"
include "cen.mm"
include "ccda.mm"
include "co.mm"
include "con0.mm"
include "harcl.mm"
include "simp3.mm"
include "cdadom3.mm"
include "sylancr.mm"
include "cfn.mm"
include "wn.mm"
include "csdm.mm"
include "domnsym.mm"
include "3ad2ant1.mm"
include "isfinite.mm"
include "sylnibr.mm"
include "pwfi.mm"
include "sylnib.mm"
include "sylancl.mm"
include "ovex.mm"
include "canth2.mm"
include "cxp.mm"
include "pwcdaen.mm"
include "cvv.mm"
include "pwexg.mm"
include "syl.mm"
include "cwdom.mm"
include "simp2.mm"
include "harwdom.mm"
include "wdompwdom.mm"
include "3syl.mm"
include "xpdom2g.mm"
include "syl2anc.mm"
include "xpexg.mm"
include "ensymd.mm"
include "enrefg.mm"
include "gchxpidm.mm"
include "pwen.mm"
include "cdaen.mm"
include "gchcdaidm.mm"
include "entr.mm"
include "domentr.mm"
include "endomtr.mm"
include "sdomdomtr.mm"
include "gchen1.mm"
include "syl22anc.mm"
include "cdacomen.mm"
include "harndom.mm"
include "domen2.mm"
include "syl5ibrcom.mm"
include "mtoi.mm"
include "brsdom.mm"
include "sylanbrc.mm"
include "canth2g.mm"
include "sdomdom.mm"
include "cdadom1.mm"
include "4syl.mm"
include "cdadom2.mm"
include "domtr.mm"
include "gchen2.mm"
include "endom.mm"
include "pwcdadom.mm"
include "sbth.mm"

theorem gchhar
  let cA: class A


  assert |- ( ( _om ~<_ A /\ A e. GCH /\ ~P A e. GCH ) -> ( har ` A ) ~~ ~P A )

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
    cA
    cpw
    #
    cgch
    wcel
    #
    w3a
    #
    cA
    char
    cfv
    #
    @2
    cdom
    wbr
    #
    @2
    @5
    cdom
    wbr
    #
    @5
    @2
    cen
    wbr
    @4
    @5
    @5
    @2
    ccda
    co
    #
    cdom
    wbr
    #
    @8
    @2
    cen
    wbr
    @6
    @4
    @5
    con0
    wcel
    #
    @3
    @9
    cA
    harcl
    #
    @0
    @1
    @3
    simp3
    #
    @5
    @2
    con0
    cgch
    cdadom3
    sylancr
    @4
    @2
    @8
    @4
    @2
    @2
    @5
    ccda
    co
    #
    cen
    wbr
    #
    @13
    @8
    cen
    wbr
    @2
    @8
    cen
    wbr
    @4
    @3
    @2
    cfn
    wcel
    #
    wn
    #
    @2
    @13
    cdom
    wbr
    #
    @13
    @2
    cpw
    #
    csdm
    wbr
    #
    @14
    @12
    @4
    cA
    cfn
    wcel
    #
    @15
    @4
    cA
    com
    csdm
    wbr
    #
    @20
    @0
    @1
    @21
    wn
    @3
    com
    cA
    domnsym
    3ad2ant1
    cA
    isfinite
    sylnibr
    #
    cA
    pwfi
    sylnib
    #
    @4
    @3
    @10
    @17
    @12
    @11
    @2
    @5
    cgch
    con0
    cdadom3
    sylancl
    @4
    @13
    @13
    cpw
    #
    csdm
    wbr
    @24
    @18
    cdom
    wbr
    #
    @19
    @13
    @2
    @5
    ccda
    ovex
    canth2
    @4
    @24
    @18
    @5
    cpw
    #
    cxp
    #
    cen
    wbr
    #
    @27
    @18
    cdom
    wbr
    #
    @25
    @4
    @3
    @10
    @28
    @12
    @11
    @2
    @5
    cgch
    con0
    pwcdaen
    sylancl
    @4
    @27
    @18
    cA
    cA
    cxp
    #
    cpw
    #
    cpw
    #
    cxp
    #
    cdom
    wbr
    #
    @33
    @18
    cen
    wbr
    #
    @29
    @4
    @18
    cvv
    wcel
    #
    @26
    @32
    cdom
    wbr
    #
    @34
    @4
    @3
    @36
    @12
    @2
    cgch
    pwexg
    syl
    @4
    @1
    @5
    @31
    cwdom
    wbr
    @37
    @0
    @1
    @3
    simp2
    #
    cgch
    cA
    harwdom
    @5
    @31
    wdompwdom
    3syl
    @26
    @32
    @18
    cvv
    xpdom2g
    syl2anc
    @4
    @33
    @2
    @31
    ccda
    co
    #
    cpw
    #
    cen
    wbr
    @40
    @18
    cen
    wbr
    #
    @35
    @4
    @40
    @33
    @4
    @3
    @31
    cvv
    wcel
    #
    @40
    @33
    cen
    wbr
    @12
    @4
    @30
    cvv
    wcel
    #
    @42
    @4
    @1
    @1
    @43
    @38
    @38
    cA
    cA
    cgch
    cgch
    xpexg
    syl2anc
    @30
    cvv
    pwexg
    syl
    @2
    @31
    cgch
    cvv
    pwcdaen
    syl2anc
    ensymd
    @4
    @39
    @2
    cen
    wbr
    #
    @41
    @4
    @39
    @2
    @2
    ccda
    co
    #
    cen
    wbr
    #
    @45
    @2
    cen
    wbr
    #
    @44
    @4
    @2
    @2
    cen
    wbr
    #
    @31
    @2
    cen
    wbr
    #
    @46
    @4
    @3
    @48
    @12
    @2
    cgch
    enrefg
    syl
    @4
    @30
    cA
    cen
    wbr
    #
    @49
    @4
    @1
    @20
    wn
    #
    @50
    @38
    @22
    cA
    gchxpidm
    syl2anc
    @30
    cA
    pwen
    syl
    @2
    @2
    @31
    @2
    cdaen
    syl2anc
    @4
    @3
    @16
    @47
    @12
    @23
    @2
    gchcdaidm
    syl2anc
    #
    @39
    @45
    @2
    entr
    syl2anc
    @39
    @2
    pwen
    syl
    @33
    @40
    @18
    entr
    syl2anc
    @27
    @33
    @18
    domentr
    syl2anc
    @24
    @27
    @18
    endomtr
    syl2anc
    @13
    @24
    @18
    sdomdomtr
    sylancr
    @2
    @13
    gchen1
    syl22anc
    @2
    @5
    cdacomen
    @2
    @13
    @8
    entr
    sylancl
    ensymd
    @5
    @8
    @2
    domentr
    syl2anc
    #
    @4
    cA
    cA
    ccda
    co
    #
    cpw
    #
    cA
    @5
    ccda
    co
    #
    cen
    wbr
    #
    @55
    @56
    cdom
    wbr
    @7
    @4
    @55
    @2
    cen
    wbr
    #
    @2
    @56
    cen
    wbr
    @57
    @4
    @54
    cA
    cen
    wbr
    #
    @58
    @4
    @1
    @51
    @59
    @38
    @22
    cA
    gchcdaidm
    syl2anc
    @54
    cA
    pwen
    syl
    @4
    @56
    @2
    @4
    @1
    @51
    cA
    @56
    csdm
    wbr
    #
    @56
    @2
    cdom
    wbr
    #
    @56
    @2
    cen
    wbr
    @38
    @22
    @4
    cA
    @56
    cdom
    wbr
    #
    cA
    @56
    cen
    wbr
    #
    wn
    @60
    @4
    @1
    @10
    @62
    @38
    @11
    cA
    @5
    cgch
    con0
    cdadom3
    sylancl
    @4
    @63
    @5
    cA
    cdom
    wbr
    #
    cA
    harndom
    @4
    @64
    @63
    @5
    @56
    cdom
    wbr
    #
    @4
    @5
    @5
    cA
    ccda
    co
    #
    cdom
    wbr
    #
    @66
    @56
    cen
    wbr
    @65
    @4
    @10
    @1
    @67
    @11
    @38
    @5
    cA
    con0
    cgch
    cdadom3
    sylancr
    @5
    cA
    cdacomen
    @5
    @66
    @56
    domentr
    sylancl
    cA
    @56
    @5
    domen2
    syl5ibrcom
    mtoi
    cA
    @56
    brsdom
    sylanbrc
    @4
    @56
    @45
    cdom
    wbr
    #
    @47
    @61
    @4
    @56
    @13
    cdom
    wbr
    #
    @13
    @45
    cdom
    wbr
    #
    @68
    @4
    @1
    cA
    @2
    csdm
    wbr
    cA
    @2
    cdom
    wbr
    @69
    @38
    cA
    cgch
    canth2g
    cA
    @2
    sdomdom
    cA
    @2
    @5
    cdadom1
    4syl
    @4
    @6
    @70
    @53
    @5
    @2
    @2
    cdadom2
    syl
    @56
    @13
    @45
    domtr
    syl2anc
    @52
    @56
    @45
    @2
    domentr
    syl2anc
    cA
    @56
    gchen2
    syl22anc
    ensymd
    @55
    @2
    @56
    entr
    syl2anc
    @55
    @56
    endom
    cA
    @5
    pwcdadom
    3syl
    @5
    @2
    sbth
    syl2anc
end
