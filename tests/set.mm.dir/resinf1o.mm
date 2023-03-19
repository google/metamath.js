include "cpi.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cneg.mm"
include "cicc.mm"
include "c1.mm"
include "ccos.mm"
include "cc0.mm"
include "cres.mm"
include "cv.mm"
include "cmin.mm"
include "cmpt.mm"
include "ccom.mm"
include "wf1o.mm"
include "csin.mm"
include "recosf1o.mm"
include "wtru.mm"
include "eqid.mm"
include "wcel.mm"
include "cr.mm"
include "cle.mm"
include "wbr.mm"
include "halfpire.mm"
include "wss.mm"
include "neghalfpire.mm"
include "iccssre.mm"
include "mp2an.mm"
include "sseli.mm"
include "resubcl.mm"
include "sylancr.mm"
include "elicc2i.mm"
include "simp3bi.mm"
include "wb.mm"
include "subge0.mm"
include "mpbird.mm"
include "recni.mm"
include "picn.mm"
include "negcli.mm"
include "caddc.mm"
include "negsubi.mm"
include "pidiv2halves.mm"
include "subaddrii.mm"
include "eqtri.mm"
include "simp2bi.mm"
include "syl5eqbr.mm"
include "pire.mm"
include "suble.mm"
include "mp3an12.mm"
include "syl.mm"
include "mpbid.mm"
include "0re.mm"
include "syl3anbrc.mm"
include "adantl.mm"
include "simp1bi.mm"
include "subnegi.mm"
include "syl6breqr.mm"
include "lesub.mm"
include "mp3an23.mm"
include "subidi.mm"
include "wa.mm"
include "wceq.mm"
include "cc.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "subsub23.mm"
include "mp3an1.mm"
include "syl2anr.mm"
include "eqcom.mm"
include "3bitr4g.mm"
include "f1o2d.mm"
include "trud.mm"
include "f1oco.mm"
include "cfv.mm"
include "wfn.mm"
include "wral.mm"
include "wf.mm"
include "cosf.mm"
include "ffn.mm"
include "ax-mp.mm"
include "fnssres.mm"
include "fmpti.mm"
include "fnfco.mm"
include "sinf.mm"
include "eqfnfv.mm"
include "ffvelrni.mm"
include "fvres.mm"
include "oveq2.mm"
include "ovex.mm"
include "fvmpt.mm"
include "fveq2d.mm"
include "coshalfpim.mm"
include "3eqtrd.mm"
include "fvco3.mm"
include "mpan.mm"
include "3eqtr4d.mm"
include "mprgbir.mm"
include "f1oeq1.mm"
include "mpbi.mm"

theorem resinf1o
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B


  assert |- ( sin |` ( -u ( _pi / 2 ) [,] ( _pi / 2 ) ) ) : ( -u ( _pi / 2 ) [,] ( _pi / 2 ) ) -1-1-onto-> ( -u 1 [,] 1 )

  proof
    cpi
    c2
    cdiv
    co
    #
    cneg
    #
    @0
    cicc
    co
    #
    c1
    cneg
    c1
    cicc
    co
    #
    ccos
    cc0
    cpi
    cicc
    co
    #
    cres
    #
    vx
    @2
    @0
    vx
    cv
    #
    cmin
    co
    #
    cmpt
    #
    ccom
    #
    wf1o
    #
    @2
    @3
    csin
    @2
    cres
    #
    wf1o
    #
    @4
    @3
    @5
    wf1o
    @2
    @4
    @8
    wf1o
    #
    @10
    recosf1o
    @13
    wtru
    vx
    vy
    @2
    @4
    @7
    @0
    vy
    cv
    #
    cmin
    co
    #
    @8
    @8
    eqid
    #
    @6
    @2
    wcel
    #
    @7
    @4
    wcel
    #
    wtru
    @17
    @7
    cr
    wcel
    #
    cc0
    @7
    cle
    wbr
    #
    @7
    cpi
    cle
    wbr
    #
    @18
    @17
    @0
    cr
    wcel
    #
    @6
    cr
    wcel
    #
    @19
    halfpire
    @2
    cr
    @6
    @1
    cr
    wcel
    #
    @22
    @2
    cr
    wss
    neghalfpire
    halfpire
    @1
    @0
    iccssre
    mp2an
    #
    sseli
    #
    @0
    @6
    resubcl
    sylancr
    @17
    @20
    @6
    @0
    cle
    wbr
    #
    @17
    @23
    @1
    @6
    cle
    wbr
    #
    @27
    @1
    @0
    @6
    neghalfpire
    halfpire
    elicc2i
    #
    simp3bi
    @17
    @22
    @23
    @20
    @27
    wb
    halfpire
    @26
    @0
    @6
    subge0
    sylancr
    mpbird
    @17
    @0
    cpi
    cmin
    co
    #
    @6
    cle
    wbr
    #
    @21
    @17
    @30
    @1
    @6
    cle
    @0
    cpi
    @1
    @0
    halfpire
    recni
    #
    picn
    @0
    @32
    negcli
    cpi
    @1
    caddc
    co
    cpi
    @0
    cmin
    co
    @0
    cpi
    @0
    picn
    @32
    negsubi
    cpi
    @0
    @0
    picn
    @32
    @32
    pidiv2halves
    subaddrii
    eqtri
    subaddrii
    @17
    @23
    @28
    @27
    @29
    simp2bi
    syl5eqbr
    @17
    @23
    @31
    @21
    wb
    #
    @26
    @22
    cpi
    cr
    wcel
    #
    @23
    @33
    halfpire
    pire
    @0
    cpi
    @6
    suble
    mp3an12
    syl
    mpbid
    cc0
    cpi
    @7
    0re
    pire
    elicc2i
    syl3anbrc
    #
    adantl
    @14
    @4
    wcel
    #
    @15
    @2
    wcel
    #
    wtru
    @36
    @15
    cr
    wcel
    #
    @1
    @15
    cle
    wbr
    #
    @15
    @0
    cle
    wbr
    #
    @37
    @36
    @22
    @14
    cr
    wcel
    #
    @38
    halfpire
    @36
    @41
    cc0
    @14
    cle
    wbr
    #
    @14
    cpi
    cle
    wbr
    #
    cc0
    cpi
    @14
    0re
    pire
    elicc2i
    #
    simp1bi
    #
    @0
    @14
    resubcl
    sylancr
    @36
    @14
    @0
    @1
    cmin
    co
    #
    cle
    wbr
    #
    @39
    @36
    @14
    cpi
    @46
    cle
    @36
    @41
    @42
    @43
    @44
    simp3bi
    @46
    @0
    @0
    caddc
    co
    cpi
    @0
    @0
    @32
    @32
    subnegi
    pidiv2halves
    eqtri
    syl6breqr
    @36
    @41
    @47
    @39
    wb
    #
    @45
    @41
    @22
    @24
    @48
    halfpire
    neghalfpire
    @14
    @0
    @1
    lesub
    mp3an23
    syl
    mpbid
    @36
    @0
    @0
    cmin
    co
    #
    @14
    cle
    wbr
    #
    @40
    @36
    @49
    cc0
    @14
    cle
    @0
    @32
    subidi
    @36
    @41
    @42
    @43
    @44
    simp2bi
    syl5eqbr
    @36
    @41
    @50
    @40
    wb
    #
    @45
    @22
    @22
    @41
    @51
    halfpire
    halfpire
    @0
    @0
    @14
    suble
    mp3an12
    syl
    mpbid
    @1
    @0
    @15
    neghalfpire
    halfpire
    elicc2i
    syl3anbrc
    adantl
    wtru
    @17
    @36
    wa
    #
    wa
    @15
    @6
    wceq
    #
    @7
    @14
    wceq
    #
    @6
    @15
    wceq
    @14
    @7
    wceq
    @52
    @53
    @54
    wb
    #
    wtru
    @36
    @14
    cc
    wcel
    #
    @6
    cc
    wcel
    #
    @55
    @17
    @4
    cc
    @14
    @4
    cr
    cc
    cc0
    cr
    wcel
    @34
    @4
    cr
    wss
    0re
    pire
    cc0
    cpi
    iccssre
    mp2an
    ax-resscn
    sstri
    #
    sseli
    @2
    cc
    @6
    @2
    cr
    cc
    @25
    ax-resscn
    sstri
    #
    sseli
    @0
    cc
    wcel
    @56
    @57
    @55
    @32
    @0
    @14
    @6
    subsub23
    mp3an1
    syl2anr
    adantl
    @6
    @15
    eqcom
    @14
    @7
    eqcom
    3bitr4g
    f1o2d
    trud
    @2
    @4
    @3
    @5
    @8
    f1oco
    mp2an
    @9
    @11
    wceq
    #
    @10
    @12
    wb
    @60
    @14
    @9
    cfv
    #
    @14
    @11
    cfv
    #
    wceq
    #
    vy
    @2
    @9
    @2
    wfn
    #
    @11
    @2
    wfn
    #
    @60
    @63
    vy
    @2
    wral
    wb
    @5
    @4
    wfn
    #
    @2
    @4
    @8
    wf
    #
    @64
    ccos
    cc
    wfn
    #
    @4
    cc
    wss
    @66
    cc
    cc
    ccos
    wf
    @68
    cosf
    cc
    cc
    ccos
    ffn
    ax-mp
    @58
    cc
    @4
    ccos
    fnssres
    mp2an
    vx
    @2
    @4
    @7
    @8
    @16
    @35
    fmpti
    #
    @4
    @2
    @5
    @8
    fnfco
    mp2an
    csin
    cc
    wfn
    #
    @2
    cc
    wss
    @65
    cc
    cc
    csin
    wf
    @70
    sinf
    cc
    cc
    csin
    ffn
    ax-mp
    @59
    cc
    @2
    csin
    fnssres
    mp2an
    vy
    @2
    @9
    @11
    eqfnfv
    mp2an
    @14
    @2
    wcel
    #
    @14
    @8
    cfv
    #
    @5
    cfv
    #
    @14
    csin
    cfv
    #
    @61
    @62
    @71
    @73
    @72
    ccos
    cfv
    #
    @15
    ccos
    cfv
    #
    @74
    @71
    @72
    @4
    wcel
    @73
    @75
    wceq
    @2
    @4
    @14
    @8
    @69
    ffvelrni
    @72
    @4
    ccos
    fvres
    syl
    @71
    @72
    @15
    ccos
    vx
    @14
    @7
    @15
    @2
    @8
    @6
    @14
    @0
    cmin
    oveq2
    @16
    @0
    @14
    cmin
    ovex
    fvmpt
    fveq2d
    @71
    @56
    @76
    @74
    wceq
    @2
    cc
    @14
    @59
    sseli
    @14
    coshalfpim
    syl
    3eqtrd
    @67
    @71
    @61
    @73
    wceq
    @69
    @2
    @4
    @14
    @5
    @8
    fvco3
    mpan
    @14
    @2
    csin
    fvres
    3eqtr4d
    mprgbir
    @2
    @3
    @9
    @11
    f1oeq1
    ax-mp
    mpbi
end
