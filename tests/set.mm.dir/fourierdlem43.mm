include "cpi.mm"
include "cneg.mm"
include "cicc.mm"
include "co.mm"
include "cr.mm"
include "cv.mm"
include "cc0.mm"
include "wceq.mm"
include "c1.mm"
include "c2.mm"
include "cdiv.mm"
include "csin.mm"
include "cfv.mm"
include "cmul.mm"
include "cif.mm"
include "wcel.mm"
include "wa.mm"
include "1red.mm"
include "wn.mm"
include "pire.mm"
include "a1i.mm"
include "renegcld.mm"
include "id.mm"
include "eliccre.mm"
include "syl3anc.mm"
include "adantr.mm"
include "2re.mm"
include "rehalfcld.mm"
include "resincld.mm"
include "remulcld.mm"
include "2cnd.mm"
include "recnd.mm"
include "wne.mm"
include "2ne0.mm"
include "clt.mm"
include "wbr.mm"
include "cioo.mm"
include "cxr.mm"
include "0xr.mm"
include "remulcli.mm"
include "rexri.mm"
include "simpr.mm"
include "cle.mm"
include "rexrd.mm"
include "iccleub.mm"
include "crp.mm"
include "pirp.mm"
include "2timesgt.mm"
include "ax-mp.mm"
include "lelttrd.mm"
include "eliood.mm"
include "sinaover2ne0.mm"
include "syl.mm"
include "adantlr.mm"
include "cico.mm"
include "ad2antrr.mm"
include "iccgelb.mm"
include "0red.mm"
include "neqne.mm"
include "ad2antlr.mm"
include "lttri5d.mm"
include "w3a.mm"
include "wb.mm"
include "elico2.mm"
include "sylancl.mm"
include "mpbir3and.mm"
include "renegcli.mm"
include "elicore.mm"
include "mpan.mm"
include "divnegd.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "negeqd.mm"
include "cc.mm"
include "halfcld.mm"
include "sinneg.mm"
include "sincld.mm"
include "negnegd.mm"
include "3eqtrd.mm"
include "negcld.mm"
include "icoltub.mm"
include "lt0neg1d.mm"
include "mpbid.mm"
include "icogelb.mm"
include "lenegcon1d.mm"
include "negne0d.mm"
include "eqnetrrd.mm"
include "pm2.61dan.mm"
include "mulne0d.mm"
include "redivcld.mm"
include "ifclda.mm"
include "fmpti.mm"

theorem fourierdlem43
  let cK: class K
  let vs: setvar s
  let vk: setvar k
  let vx: setvar x
  assume fourierdlem43.1: |- K = ( s e. ( -u _pi [,] _pi ) |-> if ( s = 0 , 1 , ( s / ( 2 x. ( sin ` ( s / 2 ) ) ) ) ) )


  assert |- K : ( -u _pi [,] _pi ) --> RR

  proof
    vs
    cpi
    cneg
    #
    cpi
    cicc
    co
    #
    cr
    vs
    cv
    #
    cc0
    wceq
    #
    c1
    @2
    c2
    @2
    c2
    cdiv
    co
    #
    csin
    cfv
    #
    cmul
    co
    #
    cdiv
    co
    #
    cif
    cK
    fourierdlem43.1
    @2
    @1
    wcel
    #
    @3
    c1
    @7
    cr
    @8
    @3
    wa
    1red
    @8
    @3
    wn
    #
    wa
    #
    @2
    @6
    @8
    @2
    cr
    wcel
    #
    @9
    @8
    @0
    cr
    wcel
    #
    cpi
    cr
    wcel
    #
    @8
    @11
    @8
    cpi
    @13
    @8
    pire
    a1i
    #
    renegcld
    #
    @14
    @8
    id
    #
    @0
    cpi
    @2
    eliccre
    syl3anc
    #
    adantr
    #
    @10
    c2
    @5
    c2
    cr
    wcel
    @10
    2re
    a1i
    @10
    @4
    @10
    @2
    @18
    rehalfcld
    resincld
    #
    remulcld
    @10
    c2
    @5
    @10
    2cnd
    @10
    @5
    @19
    recnd
    c2
    cc0
    wne
    #
    @10
    2ne0
    a1i
    @10
    cc0
    @2
    clt
    wbr
    #
    @5
    cc0
    wne
    #
    @8
    @21
    @22
    @9
    @8
    @21
    wa
    #
    @2
    cc0
    c2
    cpi
    cmul
    co
    #
    cioo
    co
    #
    wcel
    @22
    @23
    cc0
    @24
    @2
    cc0
    cxr
    wcel
    #
    @23
    0xr
    a1i
    @24
    cxr
    wcel
    #
    @23
    @24
    c2
    cpi
    2re
    pire
    remulcli
    #
    rexri
    #
    a1i
    @8
    @11
    @21
    @17
    adantr
    @8
    @21
    simpr
    @8
    @2
    @24
    clt
    wbr
    @21
    @8
    @2
    cpi
    @24
    @17
    @14
    @24
    cr
    wcel
    #
    @8
    @28
    a1i
    @8
    @0
    cxr
    wcel
    #
    cpi
    cxr
    wcel
    #
    @8
    @2
    cpi
    cle
    wbr
    @8
    @0
    @15
    rexrd
    #
    @8
    cpi
    @14
    rexrd
    #
    @16
    @0
    cpi
    @2
    iccleub
    syl3anc
    cpi
    @24
    clt
    wbr
    #
    @8
    cpi
    crp
    wcel
    @35
    pirp
    cpi
    2timesgt
    ax-mp
    #
    a1i
    lelttrd
    adantr
    eliood
    @2
    sinaover2ne0
    syl
    adantlr
    @10
    @21
    wn
    #
    wa
    #
    @2
    @0
    cc0
    cico
    co
    wcel
    #
    @22
    @38
    @39
    @11
    @0
    @2
    cle
    wbr
    #
    @2
    cc0
    clt
    wbr
    #
    @8
    @11
    @9
    @37
    @17
    ad2antrr
    #
    @8
    @40
    @9
    @37
    @8
    @31
    @32
    @8
    @40
    @33
    @34
    @16
    @0
    cpi
    @2
    iccgelb
    syl3anc
    ad2antrr
    @38
    @2
    cc0
    @42
    @38
    0red
    @9
    @2
    cc0
    wne
    @8
    @37
    @2
    cc0
    neqne
    ad2antlr
    @10
    @37
    simpr
    lttri5d
    @38
    @12
    @26
    @39
    @11
    @40
    @41
    w3a
    wb
    @8
    @12
    @9
    @37
    @15
    ad2antrr
    0xr
    @0
    cc0
    @2
    elico2
    sylancl
    mpbir3and
    @39
    @2
    cneg
    #
    c2
    cdiv
    co
    #
    csin
    cfv
    #
    cneg
    #
    @5
    cc0
    @39
    @46
    @4
    cneg
    #
    csin
    cfv
    #
    cneg
    @5
    cneg
    #
    cneg
    @5
    @39
    @45
    @48
    @39
    @44
    @47
    csin
    @39
    @47
    @44
    @39
    @2
    c2
    @39
    @2
    @12
    @39
    @11
    cpi
    pire
    renegcli
    #
    @0
    cc0
    @2
    elicore
    mpan
    #
    recnd
    #
    @39
    2cnd
    @20
    @39
    2ne0
    a1i
    divnegd
    eqcomd
    fveq2d
    negeqd
    @39
    @48
    @49
    @39
    @4
    cc
    wcel
    @48
    @49
    wceq
    @39
    @2
    @52
    halfcld
    #
    @4
    sinneg
    syl
    negeqd
    @39
    @5
    @39
    @4
    @53
    sincld
    negnegd
    3eqtrd
    @39
    @45
    @39
    @44
    @39
    @43
    @39
    @2
    @52
    negcld
    halfcld
    sincld
    @39
    @43
    @25
    wcel
    @45
    cc0
    wne
    @39
    cc0
    @24
    @43
    @26
    @39
    0xr
    a1i
    #
    @27
    @39
    @29
    a1i
    @39
    @2
    @51
    renegcld
    #
    @39
    @41
    cc0
    @43
    clt
    wbr
    @39
    @31
    @26
    @39
    @41
    @39
    @0
    @12
    @39
    @50
    a1i
    rexrd
    #
    @54
    @39
    id
    #
    @0
    cc0
    @2
    icoltub
    syl3anc
    @39
    @2
    @51
    lt0neg1d
    mpbid
    @39
    @43
    cpi
    @24
    @55
    @13
    @39
    pire
    a1i
    #
    @30
    @39
    @28
    a1i
    @39
    cpi
    @2
    @58
    @51
    @39
    @31
    @26
    @39
    @40
    @56
    @54
    @57
    @0
    cc0
    @2
    icogelb
    syl3anc
    lenegcon1d
    @35
    @39
    @36
    a1i
    lelttrd
    eliood
    @43
    sinaover2ne0
    syl
    negne0d
    eqnetrrd
    syl
    pm2.61dan
    mulne0d
    redivcld
    ifclda
    fmpti
end
