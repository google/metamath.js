include "cc0.mm"
include "c1.mm"
include "cioc.mm"
include "co.mm"
include "wcel.mm"
include "csin.mm"
include "cfv.mm"
include "c3.mm"
include "cexp.mm"
include "c6.mm"
include "cdiv.mm"
include "cmin.mm"
include "cabs.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "c4.mm"
include "cuz.mm"
include "cv.mm"
include "cn0.mm"
include "ci.mm"
include "cmul.mm"
include "cfa.mm"
include "cmpt.mm"
include "csu.mm"
include "cim.mm"
include "wceq.mm"
include "caddc.mm"
include "cr.mm"
include "cle.mm"
include "cxr.mm"
include "w3a.mm"
include "wb.mm"
include "0xr.mm"
include "1re.mm"
include "elioc2.mm"
include "mp2an.mm"
include "simp1bi.mm"
include "eqid.mm"
include "resin4p.mm"
include "syl.mm"
include "eqcomd.mm"
include "resincld.mm"
include "recnd.mm"
include "cn.mm"
include "3nn0.mm"
include "reexpcl.mm"
include "sylancl.mm"
include "6nn.mm"
include "nndivre.mm"
include "resubcld.mm"
include "cc.mm"
include "ax-icn.mm"
include "mulcl.mm"
include "sylancr.mm"
include "4nn0.mm"
include "eftlcl.mm"
include "imcld.mm"
include "subaddd.mm"
include "mpbird.mm"
include "fveq2d.mm"
include "abscld.mm"
include "absimle.mm"
include "ef01bndlem.mm"
include "a1i.mm"
include "cz.mm"
include "4z.mm"
include "3re.mm"
include "4re.mm"
include "3lt4.mm"
include "ltleii.mm"
include "3nn.mm"
include "nnzi.mm"
include "eluz1i.mm"
include "mpbir2an.mm"
include "simp2bi.mm"
include "wi.mm"
include "0re.mm"
include "ltle.mm"
include "mpd.mm"
include "simp3bi.mm"
include "leexp2rd.mm"
include "6re.mm"
include "6pos.mm"
include "lediv1.mm"
include "syl112anc.mm"
include "mpbid.mm"
include "ltletrd.mm"
include "lelttrd.mm"
include "eqbrtrd.mm"
include "absdifltd.mm"
include "subsub4d.mm"
include "c2.mm"
include "wne.mm"
include "3cn.mm"
include "3ne0.mm"
include "pm3.2i.mm"
include "2cnne0.mm"
include "divdiv1.mm"
include "mp3an23.mm"
include "3t2e6.mm"
include "oveq2i.mm"
include "syl6req.mm"
include "oveq12d.mm"
include "2halvesd.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "breq1d.mm"
include "npcand.mm"
include "breq2d.mm"
include "anbi12d.mm"
include "bitrd.mm"

theorem sin01bnd
  let cA: class A
  let vk: setvar k
  let vn: setvar n


  assert |- ( A e. ( 0 (,] 1 ) -> ( ( A - ( ( A ^ 3 ) / 3 ) ) < ( sin ` A ) /\ ( sin ` A ) < A ) )

  proof
    cA
    cc0
    c1
    cioc
    co
    wcel
    #
    cA
    csin
    cfv
    #
    cA
    cA
    c3
    cexp
    co
    #
    c6
    cdiv
    co
    #
    cmin
    co
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @3
    clt
    wbr
    #
    cA
    @2
    c3
    cdiv
    co
    #
    cmin
    co
    #
    @1
    clt
    wbr
    #
    @1
    cA
    clt
    wbr
    #
    wa
    #
    @0
    @6
    c4
    cuz
    cfv
    vk
    cv
    vn
    cn0
    ci
    cA
    cmul
    co
    #
    vn
    cv
    #
    cexp
    co
    @14
    cfa
    cfv
    cdiv
    co
    cmpt
    #
    cfv
    vk
    csu
    #
    cim
    cfv
    #
    cabs
    cfv
    #
    @3
    clt
    @0
    @5
    @17
    cabs
    @0
    @5
    @17
    wceq
    @4
    @17
    caddc
    co
    #
    @1
    wceq
    @0
    @1
    @19
    @0
    cA
    cr
    wcel
    #
    @1
    @19
    wceq
    @0
    @20
    cc0
    cA
    clt
    wbr
    #
    cA
    c1
    cle
    wbr
    #
    cc0
    cxr
    wcel
    c1
    cr
    wcel
    @0
    @20
    @21
    @22
    w3a
    wb
    0xr
    1re
    cc0
    c1
    cA
    elioc2
    mp2an
    #
    simp1bi
    #
    cA
    vk
    vn
    @15
    @15
    eqid
    #
    resin4p
    syl
    eqcomd
    @0
    @1
    @4
    @17
    @0
    @1
    @0
    cA
    @24
    resincld
    #
    recnd
    @0
    @4
    @0
    cA
    @3
    @24
    @0
    @2
    cr
    wcel
    #
    c6
    cn
    wcel
    #
    @3
    cr
    wcel
    @0
    @20
    c3
    cn0
    wcel
    #
    @27
    @24
    3nn0
    cA
    c3
    reexpcl
    sylancl
    #
    6nn
    @2
    c6
    nndivre
    sylancl
    #
    resubcld
    #
    recnd
    @0
    @17
    @0
    @16
    @0
    @13
    cc
    wcel
    #
    c4
    cn0
    wcel
    #
    @16
    cc
    wcel
    #
    @0
    ci
    cc
    wcel
    cA
    cc
    wcel
    @33
    ax-icn
    @0
    cA
    @24
    recnd
    #
    ci
    cA
    mulcl
    sylancr
    4nn0
    @13
    vk
    vn
    @15
    c4
    @25
    eftlcl
    sylancl
    #
    imcld
    recnd
    #
    subaddd
    mpbird
    fveq2d
    @0
    @18
    @16
    cabs
    cfv
    #
    @3
    @0
    @17
    @38
    abscld
    @0
    @16
    @37
    abscld
    #
    @31
    @0
    @35
    @18
    @39
    cle
    wbr
    @37
    @16
    absimle
    syl
    @0
    @39
    cA
    c4
    cexp
    co
    #
    c6
    cdiv
    co
    #
    @3
    @40
    @0
    @41
    cr
    wcel
    #
    @28
    @42
    cr
    wcel
    @0
    @20
    @34
    @43
    @24
    4nn0
    cA
    c4
    reexpcl
    sylancl
    #
    6nn
    @41
    c6
    nndivre
    sylancl
    @31
    cA
    vk
    vn
    @15
    @25
    ef01bndlem
    @0
    @41
    @2
    cle
    wbr
    #
    @42
    @3
    cle
    wbr
    #
    @0
    cA
    c3
    c4
    @24
    @29
    @0
    3nn0
    a1i
    c4
    c3
    cuz
    cfv
    wcel
    #
    @0
    @47
    c4
    cz
    wcel
    c3
    c4
    cle
    wbr
    4z
    c3
    c4
    3re
    4re
    3lt4
    ltleii
    c3
    c4
    c3
    3nn
    nnzi
    eluz1i
    mpbir2an
    a1i
    @0
    @21
    cc0
    cA
    cle
    wbr
    #
    @0
    @20
    @21
    @22
    @23
    simp2bi
    @0
    cc0
    cr
    wcel
    @20
    @21
    @48
    wi
    0re
    @24
    cc0
    cA
    ltle
    sylancr
    mpd
    @0
    @20
    @21
    @22
    @23
    simp3bi
    leexp2rd
    @0
    @43
    @27
    c6
    cr
    wcel
    #
    cc0
    c6
    clt
    wbr
    #
    @45
    @46
    wb
    @44
    @30
    @49
    @0
    6re
    a1i
    @50
    @0
    6pos
    a1i
    @41
    @2
    c6
    lediv1
    syl112anc
    mpbid
    ltletrd
    lelttrd
    eqbrtrd
    @0
    @7
    @4
    @3
    cmin
    co
    #
    @1
    clt
    wbr
    #
    @1
    @4
    @3
    caddc
    co
    #
    clt
    wbr
    #
    wa
    @12
    @0
    @1
    @4
    @3
    @26
    @32
    @31
    absdifltd
    @0
    @52
    @10
    @54
    @11
    @0
    @51
    @9
    @1
    clt
    @0
    @51
    cA
    @3
    @3
    caddc
    co
    #
    cmin
    co
    @9
    @0
    cA
    @3
    @3
    @36
    @0
    @3
    @31
    recnd
    #
    @56
    subsub4d
    @0
    @55
    @8
    cA
    cmin
    @0
    @55
    @8
    c2
    cdiv
    co
    #
    @57
    caddc
    co
    @8
    @0
    @3
    @57
    @3
    @57
    caddc
    @0
    @57
    @2
    c3
    c2
    cmul
    co
    #
    cdiv
    co
    #
    @3
    @0
    @2
    cc
    wcel
    #
    @57
    @59
    wceq
    #
    @0
    @2
    @30
    recnd
    @60
    c3
    cc
    wcel
    #
    c3
    cc0
    wne
    #
    wa
    c2
    cc
    wcel
    c2
    cc0
    wne
    wa
    @61
    @62
    @63
    3cn
    3ne0
    pm3.2i
    2cnne0
    @2
    c3
    c2
    divdiv1
    mp3an23
    syl
    @58
    c6
    @2
    cdiv
    3t2e6
    oveq2i
    syl6req
    #
    @64
    oveq12d
    @0
    @8
    @0
    @8
    @0
    @27
    c3
    cn
    wcel
    @8
    cr
    wcel
    @30
    3nn
    @2
    c3
    nndivre
    sylancl
    recnd
    2halvesd
    eqtrd
    oveq2d
    eqtrd
    breq1d
    @0
    @53
    cA
    @1
    clt
    @0
    cA
    @3
    @36
    @56
    npcand
    breq2d
    anbi12d
    bitrd
    mpbid
end
