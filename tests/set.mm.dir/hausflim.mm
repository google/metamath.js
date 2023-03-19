include "cha.mm"
include "wcel.mm"
include "ctop.mm"
include "cv.mm"
include "cflim.mm"
include "co.mm"
include "wmo.mm"
include "cfil.mm"
include "cfv.mm"
include "wral.mm"
include "wa.mm"
include "haustop.mm"
include "hausflimi.mm"
include "ralrimivw.mm"
include "jca.mm"
include "wne.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "csn.mm"
include "cnei.mm"
include "wrex.mm"
include "wi.mm"
include "wn.mm"
include "cun.mm"
include "cfi.mm"
include "cfbas.mm"
include "wb.mm"
include "ctopon.mm"
include "wss.mm"
include "simpl.mm"
include "toptopon.mm"
include "sylib.mm"
include "simprll.mm"
include "snssd.mm"
include "snnzg.mm"
include "syl.mm"
include "neifil.mm"
include "syl3anc.mm"
include "filfbas.mm"
include "simprlr.mm"
include "fbunfip.mm"
include "syl2anc.mm"
include "cpw.mm"
include "w3a.mm"
include "neisspw.mm"
include "unssd.mm"
include "adantr.mm"
include "a1d.mm"
include "ssun1.mm"
include "filn0.mm"
include "ssn0.mm"
include "sylancr.mm"
include "idd.mm"
include "3jcad.mm"
include "topopn.mm"
include "fsubbas.mm"
include "cfg.mm"
include "fgcl.mm"
include "adantl.mm"
include "simplrr.mm"
include "cvv.mm"
include "fvex.mm"
include "unex.mm"
include "ssfii.mm"
include "ax-mp.mm"
include "ssfg.mm"
include "syl5ss.mm"
include "elflim.mm"
include "mpbir2and.mm"
include "unssbd.mm"
include "eleq1.mm"
include "moi.mm"
include "3com23.mm"
include "3expia.mm"
include "syl22anc.mm"
include "necon3ad.mm"
include "mpd.mm"
include "oveq2.mm"
include "eleq2d.mm"
include "mobidv.mm"
include "notbid.mm"
include "rspcev.mm"
include "ex.mm"
include "sylbird.mm"
include "syld.mm"
include "df-ne.mm"
include "ralbii.mm"
include "ralnex.mm"
include "bitri.mm"
include "rexnal.mm"
include "3imtr3g.mm"
include "con4d.mm"
include "imp.mm"
include "an32s.mm"
include "expr.mm"
include "ralrimivva.mm"
include "hausnei2.mm"
include "mpbird.mm"
include "impbii.mm"

theorem hausflim
  let vx: setvar x
  let vf: setvar f
  let cJ: class J
  let cX: class X
  let vu: setvar u
  let vv: setvar v
  let vy: setvar y
  let cF: class F
  let vw: setvar w
  let vz: setvar z
  let cS: class S
  assume flimcf.1: |- X = U. J

  disjoint f x
  disjoint J f
  disjoint J x
  disjoint X f
  disjoint X x
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint F u
  disjoint v x
  disjoint v y
  disjoint F v
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f y
  disjoint f z
  disjoint u w
  disjoint u z
  disjoint J u
  disjoint v w
  disjoint v z
  disjoint J v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint J w
  disjoint x z
  disjoint y z
  disjoint J y
  disjoint J z
  disjoint S x
  disjoint S y
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint X z
  assert |- ( J e. Haus <-> ( J e. Top /\ A. f e. ( Fil ` X ) E* x x e. ( J fLim f ) ) )

  proof
    cJ
    cha
    wcel
    #
    cJ
    ctop
    wcel
    #
    vx
    cv
    #
    cJ
    vf
    cv
    #
    cflim
    co
    #
    wcel
    #
    vx
    wmo
    #
    vf
    cX
    cfil
    cfv
    #
    wral
    #
    wa
    #
    @0
    @1
    @8
    cJ
    haustop
    @0
    @6
    vf
    @7
    vx
    @3
    cJ
    hausflimi
    ralrimivw
    jca
    @9
    @0
    vz
    cv
    #
    vw
    cv
    #
    wne
    #
    vu
    cv
    vv
    cv
    cin
    #
    c0
    wceq
    #
    vv
    @11
    csn
    #
    cJ
    cnei
    cfv
    #
    cfv
    #
    wrex
    #
    vu
    @10
    csn
    #
    @16
    cfv
    #
    wrex
    #
    wi
    #
    vw
    cX
    wral
    vz
    cX
    wral
    #
    @9
    @22
    vz
    vw
    cX
    cX
    @9
    @10
    cX
    wcel
    #
    @11
    cX
    wcel
    #
    wa
    #
    @12
    @21
    @1
    @26
    @12
    wa
    #
    @8
    @21
    @1
    @27
    wa
    #
    @8
    @21
    @28
    @21
    @8
    @28
    @13
    c0
    wne
    #
    vv
    @17
    wral
    #
    vu
    @20
    wral
    #
    @6
    wn
    #
    vf
    @7
    wrex
    #
    @21
    wn
    #
    @8
    wn
    @28
    @31
    c0
    @20
    @17
    cun
    #
    cfi
    cfv
    #
    wcel
    wn
    #
    @33
    @28
    @20
    cX
    cfbas
    cfv
    #
    wcel
    #
    @17
    @38
    wcel
    #
    @37
    @31
    wb
    @28
    @20
    @7
    wcel
    #
    @39
    @28
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    @19
    cX
    wss
    @19
    c0
    wne
    #
    @41
    @28
    @1
    @42
    @1
    @27
    simpl
    cJ
    cX
    flimcf.1
    toptopon
    #
    sylib
    #
    @28
    @10
    cX
    @1
    @24
    @25
    @12
    simprll
    #
    snssd
    @28
    @24
    @43
    @46
    @10
    cX
    snnzg
    syl
    @19
    cJ
    cX
    neifil
    syl3anc
    #
    @20
    cX
    filfbas
    syl
    @28
    @17
    @7
    wcel
    #
    @40
    @28
    @42
    @15
    cX
    wss
    @15
    c0
    wne
    #
    @48
    @45
    @28
    @11
    cX
    @1
    @24
    @25
    @12
    simprlr
    #
    snssd
    @28
    @25
    @49
    @50
    @11
    cX
    snnzg
    syl
    @15
    cJ
    cX
    neifil
    syl3anc
    @17
    cX
    filfbas
    syl
    vu
    vv
    @20
    @17
    cX
    cX
    fbunfip
    syl2anc
    @28
    @37
    @35
    cX
    cpw
    #
    wss
    #
    @35
    c0
    wne
    #
    @37
    w3a
    #
    @33
    @28
    @37
    @52
    @53
    @37
    @28
    @52
    @37
    @1
    @52
    @27
    @1
    @20
    @17
    @51
    @19
    cJ
    cX
    flimcf.1
    neisspw
    @15
    cJ
    cX
    flimcf.1
    neisspw
    unssd
    adantr
    a1d
    @28
    @53
    @37
    @28
    @20
    @35
    wss
    @20
    c0
    wne
    #
    @53
    @20
    @17
    ssun1
    #
    @28
    @41
    @55
    @47
    @20
    cX
    filn0
    syl
    @20
    @35
    ssn0
    sylancr
    a1d
    @28
    @37
    idd
    3jcad
    @28
    @54
    @36
    @38
    wcel
    #
    @33
    @28
    cX
    cJ
    wcel
    #
    @57
    @54
    wb
    @1
    @58
    @27
    cJ
    cX
    flimcf.1
    topopn
    adantr
    @35
    cJ
    cX
    fsubbas
    syl
    @28
    @57
    @33
    @28
    @57
    wa
    #
    cX
    @36
    cfg
    co
    #
    @7
    wcel
    #
    @2
    cJ
    @60
    cflim
    co
    #
    wcel
    #
    vx
    wmo
    #
    wn
    #
    @33
    @57
    @61
    @28
    @36
    cX
    fgcl
    adantl
    #
    @59
    @12
    @65
    @1
    @26
    @12
    @57
    simplrr
    @59
    @64
    @10
    @11
    @59
    @24
    @25
    @10
    @62
    wcel
    #
    @11
    @62
    wcel
    #
    @64
    @10
    @11
    wceq
    #
    wi
    @28
    @24
    @57
    @46
    adantr
    #
    @28
    @25
    @57
    @50
    adantr
    #
    @59
    @67
    @24
    @20
    @60
    wss
    #
    @70
    @59
    @20
    @35
    @60
    @56
    @59
    @35
    @36
    @60
    @35
    cvv
    wcel
    @35
    @36
    wss
    @20
    @17
    @19
    @16
    fvex
    @15
    @16
    fvex
    unex
    @35
    cvv
    ssfii
    ax-mp
    @57
    @36
    @60
    wss
    @28
    @36
    cX
    ssfg
    adantl
    syl5ss
    #
    syl5ss
    @59
    @42
    @61
    @67
    @24
    @72
    wa
    wb
    @28
    @42
    @57
    @45
    adantr
    #
    @66
    @10
    @60
    cJ
    cX
    elflim
    syl2anc
    mpbir2and
    @59
    @68
    @25
    @17
    @60
    wss
    #
    @71
    @59
    @20
    @17
    @60
    @73
    unssbd
    @59
    @42
    @61
    @68
    @25
    @75
    wa
    wb
    @74
    @66
    @11
    @60
    cJ
    cX
    elflim
    syl2anc
    mpbir2and
    @26
    @67
    @68
    wa
    #
    @64
    @69
    @26
    @64
    @76
    @69
    @63
    @67
    @68
    vx
    @10
    @11
    cX
    cX
    @2
    @10
    @62
    eleq1
    @2
    @11
    @62
    eleq1
    moi
    3com23
    3expia
    syl22anc
    necon3ad
    mpd
    @32
    @65
    vf
    @60
    @7
    @3
    @60
    wceq
    #
    @6
    @64
    @77
    @5
    @63
    vx
    @77
    @4
    @62
    @2
    @3
    @60
    cJ
    cflim
    oveq2
    eleq2d
    mobidv
    notbid
    rspcev
    syl2anc
    ex
    sylbird
    syld
    sylbird
    @31
    @18
    wn
    #
    vu
    @20
    wral
    @34
    @30
    @78
    vu
    @20
    @30
    @14
    wn
    #
    vv
    @17
    wral
    @78
    @29
    @79
    vv
    @17
    @13
    c0
    df-ne
    ralbii
    @14
    vv
    @17
    ralnex
    bitri
    ralbii
    @18
    vu
    @20
    ralnex
    bitri
    @6
    vf
    @7
    rexnal
    3imtr3g
    con4d
    imp
    an32s
    expr
    ralrimivva
    @9
    @42
    @0
    @23
    wb
    @9
    @1
    @42
    @1
    @8
    simpl
    @44
    sylib
    vz
    vw
    vv
    vu
    cJ
    cX
    hausnei2
    syl
    mpbird
    impbii
end
