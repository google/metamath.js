include "c2.mm"
include "csqrt.mm"
include "cfv.mm"
include "cq.mm"
include "wcel.mm"
include "cv.mm"
include "cdiv.mm"
include "co.mm"
include "wceq.mm"
include "cz.mm"
include "wrex.mm"
include "cn.mm"
include "c1.mm"
include "caddc.mm"
include "clt.mm"
include "wbr.mm"
include "wne.mm"
include "wral.mm"
include "wi.mm"
include "wn.mm"
include "peano2nn.mm"
include "breq2.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "nnnlt1.mm"
include "pm2.21d.mm"
include "rgen.mm"
include "wa.mm"
include "crp.mm"
include "nnrp.mm"
include "rphalflt.mm"
include "syl.mm"
include "breq1.mm"
include "oveq2.mm"
include "neeq2d.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "com13.mm"
include "simpr.mm"
include "cc.mm"
include "zcn.mm"
include "ad2antlr.mm"
include "nncn.mm"
include "ad2antrr.mm"
include "2cnd.mm"
include "cc0.mm"
include "nnne0.mm"
include "2ne0.mm"
include "a1i.mm"
include "divcan7d.mm"
include "eqtr4d.mm"
include "simplr.mm"
include "simpll.mm"
include "sqrt2irrlem.mm"
include "simprd.mm"
include "simpld.mm"
include "oveq1.mm"
include "embantd.mm"
include "necon2bd.mm"
include "mpd.mm"
include "ex.mm"
include "necon2ad.mm"
include "ralrimdva.mm"
include "syld.mm"
include "cbvralv.mm"
include "syl6ibr.mm"
include "ceqsralv.mm"
include "sylibrd.mm"
include "ancld.mm"
include "wo.mm"
include "wb.mm"
include "cle.mm"
include "nnleltp1.mm"
include "cr.mm"
include "nnre.mm"
include "leloe.mm"
include "syl2an.mm"
include "bitr3d.mm"
include "ancoms.mm"
include "jaob.mm"
include "syl6bb.mm"
include "ralbidva.mm"
include "r19.26.mm"
include "nnind.mm"
include "ltp1d.mm"
include "df-ne.mm"
include "ralnex.mm"
include "mp2d.mm"
include "nrex.mm"
include "elq.mm"
include "rexcom.mm"
include "bitri.mm"
include "mtbir.mm"
include "nelir.mm"

theorem sqrt2irr
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( sqrt ` 2 ) e/ QQ

  proof
    c2
    csqrt
    cfv
    #
    cq
    @0
    cq
    wcel
    #
    @0
    vx
    cv
    #
    vy
    cv
    #
    cdiv
    co
    #
    wceq
    #
    vx
    cz
    wrex
    #
    vy
    cn
    wrex
    #
    @6
    vy
    cn
    @3
    cn
    wcel
    #
    vz
    cv
    #
    @3
    c1
    caddc
    co
    #
    clt
    wbr
    #
    @0
    @2
    @9
    cdiv
    co
    #
    wne
    #
    vx
    cz
    wral
    #
    wi
    #
    vz
    cn
    wral
    #
    @3
    @10
    clt
    wbr
    #
    @6
    wn
    #
    @8
    @10
    cn
    wcel
    @16
    @3
    peano2nn
    @9
    vn
    cv
    #
    clt
    wbr
    #
    @14
    wi
    #
    vz
    cn
    wral
    @9
    c1
    clt
    wbr
    #
    @14
    wi
    #
    vz
    cn
    wral
    @9
    @3
    clt
    wbr
    #
    @14
    wi
    #
    vz
    cn
    wral
    #
    @16
    @16
    vn
    vy
    @10
    @19
    c1
    wceq
    #
    @21
    @23
    vz
    cn
    @27
    @20
    @22
    @14
    @19
    c1
    @9
    clt
    breq2
    imbi1d
    ralbidv
    @19
    @3
    wceq
    #
    @21
    @25
    vz
    cn
    @28
    @20
    @24
    @14
    @19
    @3
    @9
    clt
    breq2
    imbi1d
    ralbidv
    @19
    @10
    wceq
    #
    @21
    @15
    vz
    cn
    @29
    @20
    @11
    @14
    @19
    @10
    @9
    clt
    breq2
    imbi1d
    ralbidv
    #
    @30
    @23
    vz
    cn
    @9
    cn
    wcel
    #
    @22
    @14
    @9
    nnnlt1
    pm2.21d
    rgen
    @8
    @26
    @26
    @9
    @3
    wceq
    #
    @14
    wi
    #
    vz
    cn
    wral
    #
    wa
    #
    @16
    @8
    @26
    @34
    @8
    @26
    @0
    @4
    wne
    #
    vx
    cz
    wral
    #
    @34
    @8
    @26
    @0
    @9
    @3
    cdiv
    co
    #
    wne
    #
    vz
    cz
    wral
    #
    @37
    @8
    @26
    @3
    c2
    cdiv
    co
    #
    cn
    wcel
    #
    @0
    @2
    @41
    cdiv
    co
    #
    wne
    #
    vx
    cz
    wral
    #
    wi
    #
    @40
    @8
    @41
    @3
    clt
    wbr
    #
    @26
    @46
    wi
    @8
    @3
    crp
    wcel
    @47
    @3
    nnrp
    @3
    rphalflt
    syl
    @42
    @26
    @47
    @45
    @25
    @47
    @45
    wi
    vz
    @41
    cn
    @9
    @41
    wceq
    #
    @24
    @47
    @14
    @45
    @9
    @41
    @3
    clt
    breq1
    @48
    @13
    @44
    vx
    cz
    @48
    @12
    @43
    @0
    @9
    @41
    @2
    cdiv
    oveq2
    neeq2d
    ralbidv
    imbi12d
    rspcv
    com13
    syl
    @8
    @46
    @39
    vz
    cz
    @8
    @9
    cz
    wcel
    #
    wa
    #
    @46
    @0
    @38
    @50
    @0
    @38
    wceq
    #
    @46
    wn
    #
    @50
    @51
    wa
    #
    @0
    @9
    c2
    cdiv
    co
    #
    @41
    cdiv
    co
    #
    wceq
    @52
    @53
    @0
    @38
    @55
    @50
    @51
    simpr
    #
    @53
    @9
    @3
    c2
    @49
    @9
    cc
    wcel
    @8
    @51
    @9
    zcn
    ad2antlr
    @8
    @3
    cc
    wcel
    @49
    @51
    @3
    nncn
    ad2antrr
    @53
    2cnd
    @8
    @3
    cc0
    wne
    @49
    @51
    @3
    nnne0
    ad2antrr
    c2
    cc0
    wne
    @53
    2ne0
    a1i
    divcan7d
    eqtr4d
    @53
    @46
    @0
    @55
    @53
    @42
    @45
    @0
    @55
    wne
    #
    @53
    @54
    cz
    wcel
    #
    @42
    @53
    @9
    @3
    @8
    @49
    @51
    simplr
    @8
    @49
    @51
    simpll
    @56
    sqrt2irrlem
    #
    simprd
    @53
    @58
    @45
    @57
    wi
    @53
    @58
    @42
    @59
    simpld
    @44
    @57
    vx
    @54
    cz
    @2
    @54
    wceq
    @43
    @55
    @0
    @2
    @54
    @41
    cdiv
    oveq1
    neeq2d
    rspcv
    syl
    embantd
    necon2bd
    mpd
    ex
    necon2ad
    ralrimdva
    syld
    @36
    @39
    vx
    vz
    cz
    @2
    @9
    wceq
    @4
    @38
    @0
    @2
    @9
    @3
    cdiv
    oveq1
    neeq2d
    cbvralv
    syl6ibr
    @14
    @37
    vz
    @3
    cn
    @32
    @13
    @36
    vx
    cz
    @32
    @12
    @4
    @0
    @9
    @3
    @2
    cdiv
    oveq2
    neeq2d
    #
    ralbidv
    ceqsralv
    sylibrd
    ancld
    @8
    @16
    @25
    @33
    wa
    #
    vz
    cn
    wral
    @35
    @8
    @15
    @61
    vz
    cn
    @8
    @31
    wa
    #
    @15
    @24
    @32
    wo
    #
    @14
    wi
    @61
    @62
    @11
    @63
    @14
    @31
    @8
    @11
    @63
    wb
    @31
    @8
    wa
    @9
    @3
    cle
    wbr
    #
    @11
    @63
    @9
    @3
    nnleltp1
    @31
    @9
    cr
    wcel
    @3
    cr
    wcel
    @64
    @63
    wb
    @8
    @9
    nnre
    @3
    nnre
    #
    @9
    @3
    leloe
    syl2an
    bitr3d
    ancoms
    imbi1d
    @24
    @14
    @32
    jaob
    syl6bb
    ralbidva
    @25
    @33
    vz
    cn
    r19.26
    syl6bb
    sylibrd
    nnind
    syl
    @8
    @3
    @65
    ltp1d
    @15
    @17
    @18
    wi
    vz
    @3
    cn
    @32
    @11
    @17
    @14
    @18
    @9
    @3
    @10
    clt
    breq1
    @32
    @14
    @5
    wn
    #
    vx
    cz
    wral
    @18
    @32
    @13
    @66
    vx
    cz
    @32
    @13
    @36
    @66
    @60
    @0
    @4
    df-ne
    syl6bb
    ralbidv
    @5
    vx
    cz
    ralnex
    syl6bb
    imbi12d
    rspcv
    mp2d
    nrex
    @1
    @5
    vy
    cn
    wrex
    vx
    cz
    wrex
    @7
    vx
    vy
    @0
    elq
    @5
    vx
    vy
    cz
    cn
    rexcom
    bitri
    mtbir
    nelir
end
