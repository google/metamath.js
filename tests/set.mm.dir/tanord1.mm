include "wtru.mm"
include "cc0.mm"
include "cpi.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cico.mm"
include "wcel.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "ctan.mm"
include "cfv.mm"
include "wb.mm"
include "tru.mm"
include "cv.mm"
include "fveq2.mm"
include "cr.mm"
include "cxr.mm"
include "wss.mm"
include "0re.mm"
include "halfpire.mm"
include "rexri.mm"
include "icossre.mm"
include "mp2an.mm"
include "sseli.mm"
include "ccos.mm"
include "cneg.mm"
include "cioo.mm"
include "neghalfpirx.mm"
include "pire.mm"
include "2re.mm"
include "pipos.mm"
include "2pos.mm"
include "divgt0ii.mm"
include "lt0neg2.mm"
include "ax-mp.mm"
include "mpbi.mm"
include "cle.mm"
include "df-ioo.mm"
include "df-ico.mm"
include "xrltletr.mm"
include "ixxss1.mm"
include "cosq14gt0.mm"
include "syl.mm"
include "gt0ne0d.mm"
include "retancld.mm"
include "adantl.mm"
include "wi.mm"
include "w3a.mm"
include "csin.mm"
include "resincld.mm"
include "recoscld.mm"
include "redivcld.mm"
include "3ad2ant1.mm"
include "3ad2ant2.mm"
include "wne.mm"
include "cicc.mm"
include "ioossicc.mm"
include "sstri.mm"
include "sinord.mm"
include "syl2an.mm"
include "biimp3a.mm"
include "ltdiv1.mm"
include "syl112anc.mm"
include "mpbid.mm"
include "crp.mm"
include "pirp.mm"
include "rphalflt.mm"
include "df-icc.mm"
include "xrlttr.mm"
include "xrltle.mm"
include "3adant2.mm"
include "syld.mm"
include "ixxss2.mm"
include "cosord.mm"
include "0red.mm"
include "simp1.mm"
include "elico2.mm"
include "sylib.mm"
include "simp2d.mm"
include "simp3.mm"
include "lelttrd.mm"
include "simp2.mm"
include "simp3d.mm"
include "0xr.mm"
include "elioo2.mm"
include "syl3anbrc.mm"
include "sincosq1sgn.mm"
include "simprd.mm"
include "simpld.mm"
include "ltdiv2.mm"
include "syl222anc.mm"
include "lttrd.mm"
include "wceq.mm"
include "cc.mm"
include "recnd.mm"
include "tanval.mm"
include "syl2anc.mm"
include "3brtr4d.mm"
include "3expia.mm"
include "ltord1.mm"
include "mpan.mm"

theorem tanord1
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A e. ( 0 [,) ( _pi / 2 ) ) /\ B e. ( 0 [,) ( _pi / 2 ) ) ) -> ( A < B <-> ( tan ` A ) < ( tan ` B ) ) )

  proof
    wtru
    cA
    cc0
    cpi
    c2
    cdiv
    co
    #
    cico
    co
    #
    wcel
    cB
    @1
    wcel
    wa
    cA
    cB
    clt
    wbr
    cA
    ctan
    cfv
    #
    cB
    ctan
    cfv
    #
    clt
    wbr
    wb
    tru
    wtru
    vx
    vy
    vx
    cv
    #
    ctan
    cfv
    #
    vy
    cv
    #
    ctan
    cfv
    #
    cA
    cB
    @1
    @2
    @3
    @4
    @6
    ctan
    fveq2
    @4
    cA
    ctan
    fveq2
    @4
    cB
    ctan
    fveq2
    cc0
    cr
    wcel
    #
    @0
    cxr
    wcel
    #
    @1
    cr
    wss
    0re
    @0
    halfpire
    rexri
    #
    cc0
    @0
    icossre
    mp2an
    #
    @4
    @1
    wcel
    #
    @5
    cr
    wcel
    wtru
    @12
    @4
    @1
    cr
    @4
    @11
    sseli
    #
    @12
    @4
    ccos
    cfv
    #
    @12
    @4
    @0
    cneg
    #
    @0
    cioo
    co
    #
    wcel
    cc0
    @14
    clt
    wbr
    #
    @1
    @16
    @4
    @15
    cxr
    wcel
    @15
    cc0
    clt
    wbr
    #
    @1
    @16
    wss
    neghalfpirx
    cc0
    @0
    clt
    wbr
    #
    @18
    cpi
    c2
    pire
    2re
    pipos
    2pos
    divgt0ii
    @0
    cr
    wcel
    @19
    @18
    wb
    halfpire
    @0
    lt0neg2
    ax-mp
    mpbi
    vx
    vy
    vz
    vw
    @15
    cc0
    @0
    cico
    clt
    clt
    cle
    cioo
    clt
    vx
    vy
    vz
    df-ioo
    vx
    vy
    vz
    df-ico
    #
    @15
    cc0
    vw
    cv
    #
    xrltletr
    ixxss1
    mp2an
    #
    sseli
    @4
    cosq14gt0
    syl
    #
    gt0ne0d
    #
    retancld
    adantl
    @12
    @6
    @1
    wcel
    #
    wa
    @4
    @6
    clt
    wbr
    #
    @5
    @7
    clt
    wbr
    #
    wi
    wtru
    @12
    @25
    @26
    @27
    @12
    @25
    @26
    w3a
    #
    @4
    csin
    cfv
    #
    @14
    cdiv
    co
    #
    @6
    csin
    cfv
    #
    @6
    ccos
    cfv
    #
    cdiv
    co
    #
    @5
    @7
    clt
    @28
    @30
    @31
    @14
    cdiv
    co
    #
    @33
    @12
    @25
    @30
    cr
    wcel
    @26
    @12
    @29
    @14
    @12
    @4
    @13
    resincld
    @12
    @4
    @13
    recoscld
    #
    @24
    redivcld
    3ad2ant1
    @28
    @31
    @14
    @28
    @6
    @25
    @12
    @6
    cr
    wcel
    #
    @26
    @1
    cr
    @6
    @11
    sseli
    #
    3ad2ant2
    #
    resincld
    #
    @12
    @25
    @14
    cr
    wcel
    #
    @26
    @35
    3ad2ant1
    #
    @12
    @25
    @14
    cc0
    wne
    #
    @26
    @24
    3ad2ant1
    redivcld
    @28
    @31
    @32
    @39
    @28
    @6
    @38
    recoscld
    #
    @25
    @12
    @32
    cc0
    wne
    #
    @26
    @25
    @32
    @25
    @6
    @16
    wcel
    cc0
    @32
    clt
    wbr
    #
    @1
    @16
    @6
    @22
    sseli
    @6
    cosq14gt0
    syl
    gt0ne0d
    3ad2ant2
    #
    redivcld
    @28
    @29
    @31
    clt
    wbr
    #
    @30
    @34
    clt
    wbr
    #
    @12
    @25
    @26
    @47
    @12
    @4
    @15
    @0
    cicc
    co
    #
    wcel
    @6
    @49
    wcel
    @26
    @47
    wb
    @25
    @1
    @49
    @4
    @1
    @16
    @49
    @22
    @15
    @0
    ioossicc
    sstri
    #
    sseli
    @1
    @49
    @6
    @50
    sseli
    @4
    @6
    sinord
    syl2an
    biimp3a
    @28
    @29
    cr
    wcel
    @31
    cr
    wcel
    #
    @40
    @17
    @47
    @48
    wb
    @28
    @4
    @12
    @25
    @4
    cr
    wcel
    #
    @26
    @13
    3ad2ant1
    #
    resincld
    @39
    @41
    @12
    @25
    @17
    @26
    @23
    3ad2ant1
    #
    @29
    @31
    @14
    ltdiv1
    syl112anc
    mpbid
    @28
    @32
    @14
    clt
    wbr
    #
    @34
    @33
    clt
    wbr
    #
    @12
    @25
    @26
    @55
    @12
    @4
    cc0
    cpi
    cicc
    co
    #
    wcel
    @6
    @57
    wcel
    @26
    @55
    wb
    @25
    @1
    @57
    @4
    cpi
    cxr
    wcel
    #
    @0
    cpi
    clt
    wbr
    #
    @1
    @57
    wss
    cpi
    pire
    rexri
    cpi
    crp
    wcel
    @59
    pirp
    cpi
    rphalflt
    ax-mp
    vx
    vy
    vz
    vw
    cc0
    @0
    cpi
    cico
    cle
    cle
    clt
    cicc
    clt
    vx
    vy
    vz
    df-icc
    @20
    @21
    cxr
    wcel
    #
    @9
    @58
    w3a
    @21
    @0
    clt
    wbr
    @59
    wa
    @21
    cpi
    clt
    wbr
    #
    @21
    cpi
    cle
    wbr
    #
    @21
    @0
    cpi
    xrlttr
    @60
    @58
    @61
    @62
    wi
    @9
    @21
    cpi
    xrltle
    3adant2
    syld
    ixxss2
    mp2an
    #
    sseli
    @1
    @57
    @6
    @63
    sseli
    @4
    @6
    cosord
    syl2an
    biimp3a
    @28
    @32
    cr
    wcel
    @45
    @40
    @17
    @51
    cc0
    @31
    clt
    wbr
    #
    @55
    @56
    wb
    @43
    @28
    @64
    @45
    @28
    @6
    cc0
    @0
    cioo
    co
    wcel
    #
    @64
    @45
    wa
    @28
    @36
    cc0
    @6
    clt
    wbr
    #
    @6
    @0
    clt
    wbr
    #
    @65
    @38
    @28
    cc0
    @4
    @6
    @28
    0red
    @53
    @38
    @28
    @52
    cc0
    @4
    cle
    wbr
    #
    @4
    @0
    clt
    wbr
    #
    @28
    @12
    @52
    @68
    @69
    w3a
    #
    @12
    @25
    @26
    simp1
    @8
    @9
    @12
    @70
    wb
    0re
    @10
    cc0
    @0
    @4
    elico2
    mp2an
    sylib
    simp2d
    @12
    @25
    @26
    simp3
    lelttrd
    @28
    @36
    cc0
    @6
    cle
    wbr
    #
    @67
    @28
    @25
    @36
    @71
    @67
    w3a
    #
    @12
    @25
    @26
    simp2
    @8
    @9
    @25
    @72
    wb
    0re
    @10
    cc0
    @0
    @6
    elico2
    mp2an
    sylib
    simp3d
    cc0
    cxr
    wcel
    @9
    @65
    @36
    @66
    @67
    w3a
    wb
    0xr
    @10
    cc0
    @0
    @6
    elioo2
    mp2an
    syl3anbrc
    @6
    sincosq1sgn
    syl
    #
    simprd
    @41
    @54
    @39
    @28
    @64
    @45
    @73
    simpld
    @32
    @14
    @31
    ltdiv2
    syl222anc
    mpbid
    lttrd
    @12
    @25
    @5
    @30
    wceq
    #
    @26
    @12
    @4
    cc
    wcel
    @42
    @74
    @12
    @4
    @13
    recnd
    @24
    @4
    tanval
    syl2anc
    3ad2ant1
    @28
    @6
    cc
    wcel
    #
    @44
    @7
    @33
    wceq
    @25
    @12
    @75
    @26
    @25
    @6
    @37
    recnd
    3ad2ant2
    @46
    @6
    tanval
    syl2anc
    3brtr4d
    3expia
    adantl
    ltord1
    mpan
end
