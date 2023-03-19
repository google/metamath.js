include "cv.mm"
include "csin.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "c2.mm"
include "c4.mm"
include "cioo.mm"
include "co.mm"
include "wrex.mm"
include "cpi.mm"
include "wcel.mm"
include "wa.mm"
include "wtru.mm"
include "cc.mm"
include "cr.mm"
include "2re.mm"
include "a1i.mm"
include "4re.mm"
include "0re.mm"
include "clt.mm"
include "wbr.mm"
include "2lt4.mm"
include "cicc.mm"
include "wss.mm"
include "iccssre.mm"
include "mp2an.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "ccncf.mm"
include "sincn.mm"
include "sseli.mm"
include "resincld.mm"
include "adantl.mm"
include "sin4lt0.mm"
include "ccos.mm"
include "sincos2sgn.mm"
include "simpli.mm"
include "pm3.2i.mm"
include "ivth2.mm"
include "trud.mm"
include "cle.mm"
include "crp.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cin.mm"
include "cinf.mm"
include "df-pi.mm"
include "elioore.mm"
include "adantr.mm"
include "2pos.mm"
include "eliooord.mm"
include "simpld.mm"
include "lttrd.mm"
include "elrpd.mm"
include "simpr.mm"
include "pilem1.mm"
include "sylanbrc.mm"
include "wral.mm"
include "inss1.mm"
include "rpssre.mm"
include "rpge0d.mm"
include "rgen.mm"
include "breq1.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "infrelb.mm"
include "mp3an12.mm"
include "syl.mm"
include "syl5eqbr.mm"
include "caddc.mm"
include "cdiv.mm"
include "wn.mm"
include "simplll.mm"
include "sylib.mm"
include "simpllr.mm"
include "simprd.mm"
include "simplr.mm"
include "pilem2.mm"
include "ralrimiva.mm"
include "c0.mm"
include "wne.mm"
include "wb.mm"
include "ne0i.mm"
include "infrecl.mm"
include "mp3an13.mm"
include "syl5eqel.mm"
include "readdcld.mm"
include "rehalfcld.mm"
include "infregelb.mm"
include "syl31anc.mm"
include "mpbird.mm"
include "syl6breqr.mm"
include "ex.mm"
include "ltnled.mm"
include "recnd.mm"
include "addcomd.mm"
include "oveq1d.mm"
include "breq1d.mm"
include "avgle2.mm"
include "syl2anc.mm"
include "bitr4d.mm"
include "3imtr3d.mm"
include "pm2.18d.mm"
include "letri3d.mm"
include "mpbir2and.mm"
include "simpl.mm"
include "eqeltrd.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "jca.mm"
include "rexlimiva.mm"
include "ax-mp.mm"

theorem pilem3
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( _pi e. ( 2 (,) 4 ) /\ ( sin ` _pi ) = 0 )

  proof
    vx
    cv
    #
    csin
    cfv
    #
    cc0
    wceq
    #
    vx
    c2
    c4
    cioo
    co
    #
    wrex
    #
    cpi
    @3
    wcel
    #
    cpi
    csin
    cfv
    #
    cc0
    wceq
    #
    wa
    #
    @4
    wtru
    vy
    c2
    c4
    cc
    cc0
    csin
    vx
    c2
    cr
    wcel
    #
    wtru
    2re
    a1i
    c4
    cr
    wcel
    #
    wtru
    4re
    a1i
    cc0
    cr
    wcel
    #
    wtru
    0re
    a1i
    c2
    c4
    clt
    wbr
    wtru
    2lt4
    a1i
    c2
    c4
    cicc
    co
    #
    cc
    wss
    wtru
    @12
    cr
    cc
    @9
    @10
    @12
    cr
    wss
    2re
    4re
    c2
    c4
    iccssre
    mp2an
    #
    ax-resscn
    sstri
    a1i
    csin
    cc
    cc
    ccncf
    co
    wcel
    wtru
    sincn
    a1i
    vy
    cv
    #
    @12
    wcel
    #
    @14
    csin
    cfv
    #
    cr
    wcel
    wtru
    @15
    @14
    @12
    cr
    @14
    @13
    sseli
    resincld
    adantl
    c4
    csin
    cfv
    cc0
    clt
    wbr
    #
    cc0
    c2
    csin
    cfv
    clt
    wbr
    #
    wa
    wtru
    @17
    @18
    sin4lt0
    @18
    c2
    ccos
    cfv
    cc0
    clt
    wbr
    sincos2sgn
    simpli
    pm3.2i
    a1i
    ivth2
    trud
    @2
    @8
    vx
    @3
    @0
    @3
    wcel
    #
    @2
    wa
    #
    @5
    @7
    @20
    cpi
    @0
    @3
    @20
    cpi
    @0
    wceq
    cpi
    @0
    cle
    wbr
    @0
    cpi
    cle
    wbr
    #
    @20
    cpi
    crp
    csin
    ccnv
    cc0
    csn
    cima
    #
    cin
    #
    cr
    clt
    cinf
    #
    @0
    cle
    df-pi
    @20
    @0
    @23
    wcel
    #
    @24
    @0
    cle
    wbr
    #
    @20
    @0
    crp
    wcel
    @2
    @25
    @20
    @0
    @19
    @0
    cr
    wcel
    #
    @2
    @0
    c2
    c4
    elioore
    adantr
    #
    @20
    cc0
    c2
    @0
    @11
    @20
    0re
    a1i
    @9
    @20
    2re
    a1i
    @28
    cc0
    c2
    clt
    wbr
    @20
    2pos
    a1i
    @19
    c2
    @0
    clt
    wbr
    #
    @2
    @19
    @29
    @0
    c4
    clt
    wbr
    @0
    c2
    c4
    eliooord
    simpld
    adantr
    lttrd
    elrpd
    @19
    @2
    simpr
    #
    @0
    pilem1
    sylanbrc
    #
    @23
    cr
    wss
    #
    @14
    vz
    cv
    #
    cle
    wbr
    #
    vz
    @23
    wral
    #
    vy
    cr
    wrex
    #
    @25
    @26
    @23
    crp
    cr
    crp
    @22
    inss1
    #
    rpssre
    sstri
    #
    @11
    cc0
    @33
    cle
    wbr
    #
    vz
    @23
    wral
    #
    @36
    0re
    @39
    vz
    @23
    @33
    @23
    wcel
    @33
    @23
    crp
    @33
    @37
    sseli
    rpge0d
    rgen
    @35
    @40
    vy
    cc0
    cr
    @14
    cc0
    wceq
    @34
    @39
    vz
    @23
    @14
    cc0
    @33
    cle
    breq1
    ralbidv
    rspcev
    mp2an
    #
    vy
    vz
    @0
    @23
    infrelb
    mp3an12
    syl
    syl5eqbr
    @20
    @21
    @20
    cpi
    @0
    clt
    wbr
    #
    cpi
    @0
    caddc
    co
    #
    c2
    cdiv
    co
    #
    cpi
    cle
    wbr
    #
    @21
    wn
    @21
    @20
    @42
    @45
    @20
    @42
    wa
    #
    @44
    @24
    cpi
    cle
    @46
    @44
    @24
    cle
    wbr
    #
    @44
    @14
    cle
    wbr
    #
    vy
    @23
    wral
    #
    @46
    @48
    vy
    @23
    @46
    @14
    @23
    wcel
    #
    wa
    #
    @0
    @14
    @19
    @2
    @42
    @50
    simplll
    @51
    @14
    crp
    wcel
    #
    @16
    cc0
    wceq
    #
    @51
    @50
    @52
    @53
    wa
    @46
    @50
    simpr
    @14
    pilem1
    sylib
    #
    simpld
    @19
    @2
    @42
    @50
    simpllr
    @51
    @52
    @53
    @54
    simprd
    @20
    @42
    @50
    simplr
    pilem2
    ralrimiva
    @46
    @32
    @23
    c0
    wne
    #
    @36
    @44
    cr
    wcel
    @47
    @49
    wb
    @32
    @46
    @38
    a1i
    @20
    @55
    @42
    @20
    @25
    @55
    @31
    @23
    @0
    ne0i
    syl
    #
    adantr
    @36
    @46
    @41
    a1i
    @46
    @43
    @20
    @43
    cr
    wcel
    @42
    @20
    cpi
    @0
    @20
    cpi
    @24
    cr
    df-pi
    @20
    @55
    @24
    cr
    wcel
    #
    @56
    @32
    @55
    @36
    @57
    @38
    @41
    vy
    vz
    @23
    infrecl
    mp3an13
    syl
    syl5eqel
    #
    @28
    readdcld
    adantr
    rehalfcld
    vy
    vz
    vy
    @23
    @44
    infregelb
    syl31anc
    mpbird
    df-pi
    syl6breqr
    ex
    @20
    cpi
    @0
    @58
    @28
    ltnled
    @20
    @45
    @0
    cpi
    caddc
    co
    #
    c2
    cdiv
    co
    #
    cpi
    cle
    wbr
    #
    @21
    @20
    @44
    @60
    cpi
    cle
    @20
    @43
    @59
    c2
    cdiv
    @20
    cpi
    @0
    @20
    cpi
    @58
    recnd
    @20
    @0
    @28
    recnd
    addcomd
    oveq1d
    breq1d
    @20
    @27
    cpi
    cr
    wcel
    @21
    @61
    wb
    @28
    @58
    @0
    cpi
    avgle2
    syl2anc
    bitr4d
    3imtr3d
    pm2.18d
    @20
    cpi
    @0
    @58
    @28
    letri3d
    mpbir2and
    #
    @19
    @2
    simpl
    eqeltrd
    @20
    @6
    @1
    cc0
    @20
    cpi
    @0
    csin
    @62
    fveq2d
    @30
    eqtrd
    jca
    rexlimiva
    ax-mp
end
