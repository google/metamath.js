include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "cpnf.mm"
include "wf1o.mm"
include "ccnv.mm"
include "cv.mm"
include "wceq.mm"
include "caddc.mm"
include "cdiv.mm"
include "cif.mm"
include "cmpt.mm"
include "wa.mm"
include "wtru.mm"
include "cmin.mm"
include "wcel.mm"
include "cxr.mm"
include "cle.mm"
include "wbr.mm"
include "0xr.mm"
include "pnfxr.mm"
include "0lepnf.mm"
include "ubicc2.mm"
include "mp3an.mm"
include "a1i.mm"
include "wn.mm"
include "cico.mm"
include "icossicc.mm"
include "csn.mm"
include "wo.mm"
include "wi.mm"
include "cun.mm"
include "1re.mm"
include "rexri.mm"
include "0le1.mm"
include "snunico.mm"
include "eleq2i.mm"
include "elun.mm"
include "bitr3i.mm"
include "pm2.53.mm"
include "sylbi.mm"
include "elsni.mm"
include "syl6.mm"
include "con1d.mm"
include "imp.mm"
include "wral.mm"
include "wf.mm"
include "eqid.mm"
include "icopnfcnv.mm"
include "simpli.mm"
include "f1of.mm"
include "ax-mp.mm"
include "fmpt.mm"
include "mpbir.mm"
include "rspec.mm"
include "syl.mm"
include "sseldi.mm"
include "ifclda.mm"
include "adantl.mm"
include "1elunit.mm"
include "f1ocnv.mm"
include "mp2b.mm"
include "simpri.mm"
include "wb.mm"
include "eqeq2.mm"
include "bibi1d.mm"
include "simpr.mm"
include "iftrue.mm"
include "eqeq2d.mm"
include "syl5ibrcom.mm"
include "cr.mm"
include "wnel.mm"
include "pnfnre.mm"
include "neleq1.mm"
include "mpbiri.mm"
include "syl5ibcom.mm"
include "df-nel.mm"
include "iffalse.mm"
include "rge0ssre.mm"
include "eqeltrd.mm"
include "ex.mm"
include "ad2antrr.mm"
include "syl5bi.mm"
include "syld.mm"
include "impbid.mm"
include "bibi2d.mm"
include "wne.mm"
include "clt.mm"
include "w3a.mm"
include "0re.mm"
include "elico2.mm"
include "mp2an.mm"
include "sylib.mm"
include "simp1d.mm"
include "simp3d.mm"
include "gtned.mm"
include "adantll.mm"
include "neneqd.mm"
include "eqeq1.mm"
include "notbid.mm"
include "simplr.mm"
include "2falsed.mm"
include "cfv.mm"
include "f1ocnvfvb.mm"
include "mp3an1.mm"
include "cvv.mm"
include "simpl.mm"
include "ovex.mm"
include "fvmpt2.mm"
include "sylancl.mm"
include "eqeq1d.mm"
include "3bitr3rd.mm"
include "eqcom.mm"
include "3bitr4g.mm"
include "syl2an.mm"
include "an4s.mm"
include "anass1rs.mm"
include "ifbothda.mm"
include "f1ocnv2d.mm"
include "trud.mm"

theorem iccpnfcnv
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cA: class A
  let cB: class B
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  let cG: class G
  let cJ: class J
  assume iccpnfhmeo.f: |- F = ( x e. ( 0 [,] 1 ) |-> if ( x = 1 , +oo , ( x / ( 1 - x ) ) ) )

  disjoint x y
  disjoint F y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint v w
  disjoint v y
  disjoint v z
  disjoint F v
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint y z
  disjoint F z
  disjoint G w
  disjoint G z
  disjoint v x
  disjoint J v
  disjoint w x
  disjoint J w
  disjoint x z
  disjoint J x
  disjoint J y
  disjoint J z
  assert |- ( F : ( 0 [,] 1 ) -1-1-onto-> ( 0 [,] +oo ) /\ `' F = ( y e. ( 0 [,] +oo ) |-> if ( y = +oo , 1 , ( y / ( 1 + y ) ) ) ) )

  proof
    cc0
    c1
    cicc
    co
    #
    cc0
    cpnf
    cicc
    co
    #
    cF
    wf1o
    cF
    ccnv
    vy
    @1
    vy
    cv
    #
    cpnf
    wceq
    #
    c1
    @2
    c1
    @2
    caddc
    co
    #
    cdiv
    co
    #
    cif
    #
    cmpt
    wceq
    wa
    wtru
    vx
    vy
    @0
    @1
    vx
    cv
    #
    c1
    wceq
    #
    cpnf
    @7
    c1
    @7
    cmin
    co
    #
    cdiv
    co
    #
    cif
    #
    @6
    cF
    iccpnfhmeo.f
    @7
    @0
    wcel
    #
    @11
    @1
    wcel
    wtru
    @12
    @8
    cpnf
    @10
    @1
    cpnf
    @1
    wcel
    #
    @12
    @8
    wa
    cc0
    cxr
    wcel
    #
    cpnf
    cxr
    wcel
    #
    cc0
    cpnf
    cle
    wbr
    #
    @13
    0xr
    pnfxr
    0lepnf
    cc0
    cpnf
    ubicc2
    mp3an
    a1i
    @12
    @8
    wn
    #
    wa
    #
    cc0
    cpnf
    cico
    co
    #
    @1
    @10
    cc0
    cpnf
    icossicc
    @18
    @7
    cc0
    c1
    cico
    co
    #
    wcel
    #
    @10
    @19
    wcel
    #
    @12
    @17
    @21
    @12
    @21
    @8
    @12
    @21
    wn
    #
    @7
    c1
    csn
    #
    wcel
    #
    @8
    @12
    @21
    @25
    wo
    #
    @23
    @25
    wi
    @12
    @7
    @20
    @24
    cun
    #
    wcel
    @26
    @27
    @0
    @7
    @14
    c1
    cxr
    wcel
    #
    cc0
    c1
    cle
    wbr
    @27
    @0
    wceq
    0xr
    c1
    1re
    rexri
    #
    0le1
    cc0
    c1
    snunico
    mp3an
    eleq2i
    @7
    @20
    @24
    elun
    bitr3i
    @21
    @25
    pm2.53
    sylbi
    @7
    c1
    elsni
    syl6
    con1d
    imp
    #
    @22
    vx
    @20
    @22
    vx
    @20
    wral
    @20
    @19
    vx
    @20
    @10
    cmpt
    #
    wf
    #
    @20
    @19
    @31
    wf1o
    #
    @32
    @33
    @31
    ccnv
    #
    vy
    @19
    @5
    cmpt
    wceq
    #
    vx
    vy
    @31
    @31
    eqid
    #
    icopnfcnv
    #
    simpli
    #
    @20
    @19
    @31
    f1of
    ax-mp
    vx
    @20
    @19
    @10
    @31
    @36
    fmpt
    mpbir
    rspec
    syl
    #
    sseldi
    ifclda
    adantl
    @2
    @1
    wcel
    #
    @6
    @0
    wcel
    wtru
    @40
    @3
    c1
    @5
    @0
    c1
    @0
    wcel
    @40
    @3
    wa
    1elunit
    a1i
    @40
    @3
    wn
    #
    wa
    #
    @20
    @0
    @5
    cc0
    c1
    icossicc
    @42
    @2
    @19
    wcel
    #
    @5
    @20
    wcel
    #
    @40
    @41
    @43
    @40
    @43
    @3
    @40
    @43
    wn
    #
    @2
    cpnf
    csn
    #
    wcel
    #
    @3
    @40
    @43
    @47
    wo
    #
    @45
    @47
    wi
    @40
    @2
    @19
    @46
    cun
    #
    wcel
    @48
    @49
    @1
    @2
    @14
    @15
    @16
    @49
    @1
    wceq
    0xr
    pnfxr
    0lepnf
    cc0
    cpnf
    snunico
    mp3an
    eleq2i
    @2
    @19
    @46
    elun
    bitr3i
    @43
    @47
    pm2.53
    sylbi
    @2
    cpnf
    elsni
    syl6
    con1d
    imp
    #
    @44
    vy
    @19
    @44
    vy
    @19
    wral
    @19
    @20
    @34
    wf
    #
    @33
    @19
    @20
    @34
    wf1o
    @51
    @38
    @20
    @19
    @31
    f1ocnv
    @19
    @20
    @34
    f1of
    mp2b
    vy
    @19
    @20
    @5
    @34
    @33
    @35
    @37
    simpri
    #
    fmpt
    mpbir
    rspec
    syl
    #
    sseldi
    ifclda
    adantl
    @12
    @40
    wa
    #
    @7
    @6
    wceq
    #
    @2
    @11
    wceq
    #
    wb
    #
    wtru
    @3
    @8
    @56
    wb
    @7
    @5
    wceq
    #
    @56
    wb
    #
    @57
    @54
    c1
    @5
    c1
    @6
    wceq
    @8
    @55
    @56
    c1
    @6
    @7
    eqeq2
    bibi1d
    @5
    @6
    wceq
    @58
    @55
    @56
    @5
    @6
    @7
    eqeq2
    bibi1d
    @54
    @3
    wa
    #
    @8
    @56
    @60
    @56
    @8
    @3
    @54
    @3
    simpr
    @8
    @11
    cpnf
    @2
    @8
    cpnf
    @10
    iftrue
    eqeq2d
    syl5ibrcom
    @60
    @56
    @11
    cr
    wnel
    #
    @8
    @60
    @2
    cr
    wnel
    #
    @56
    @61
    @60
    @62
    cpnf
    cr
    wnel
    #
    pnfnre
    @3
    @62
    @63
    wb
    @54
    @2
    cpnf
    cr
    neleq1
    adantl
    mpbiri
    @2
    @11
    cr
    neleq1
    syl5ibcom
    @61
    @11
    cr
    wcel
    #
    wn
    @60
    @8
    @11
    cr
    df-nel
    @60
    @8
    @64
    @12
    @17
    @64
    wi
    @40
    @3
    @12
    @17
    @64
    @18
    @11
    @10
    cr
    @17
    @11
    @10
    wceq
    @12
    @8
    cpnf
    @10
    iffalse
    adantl
    @18
    @19
    cr
    @10
    rge0ssre
    @39
    sseldi
    eqeltrd
    ex
    ad2antrr
    con1d
    syl5bi
    syld
    impbid
    @8
    @58
    @3
    wb
    @58
    @2
    @10
    wceq
    #
    wb
    #
    @59
    @54
    @41
    wa
    #
    cpnf
    @10
    cpnf
    @11
    wceq
    @3
    @56
    @58
    cpnf
    @11
    @2
    eqeq2
    bibi2d
    @10
    @11
    wceq
    @65
    @56
    @58
    @10
    @11
    @2
    eqeq2
    bibi2d
    @67
    @8
    wa
    @58
    @3
    @67
    @8
    @58
    wn
    #
    @67
    @68
    @8
    c1
    @5
    wceq
    #
    wn
    @67
    c1
    @5
    @40
    @41
    c1
    @5
    wne
    @12
    @42
    @5
    c1
    @42
    @5
    cr
    wcel
    #
    cc0
    @5
    cle
    wbr
    #
    @5
    c1
    clt
    wbr
    #
    @42
    @44
    @70
    @71
    @72
    w3a
    #
    @53
    cc0
    cr
    wcel
    @28
    @44
    @73
    wb
    0re
    @29
    cc0
    c1
    @5
    elico2
    mp2an
    sylib
    #
    simp1d
    @42
    @70
    @71
    @72
    @74
    simp3d
    gtned
    adantll
    neneqd
    @8
    @58
    @69
    @7
    c1
    @5
    eqeq1
    notbid
    syl5ibrcom
    imp
    @54
    @41
    @8
    simplr
    2falsed
    @54
    @17
    @41
    @66
    @12
    @17
    @40
    @41
    @66
    @18
    @21
    @43
    @66
    @42
    @30
    @50
    @21
    @43
    wa
    #
    @5
    @7
    wceq
    #
    @10
    @2
    wceq
    #
    @58
    @65
    @75
    @7
    @31
    cfv
    #
    @2
    wceq
    #
    @2
    @34
    cfv
    #
    @7
    wceq
    #
    @77
    @76
    @33
    @21
    @43
    @79
    @81
    wb
    @38
    @20
    @19
    @7
    @2
    @31
    f1ocnvfvb
    mp3an1
    @75
    @78
    @10
    @2
    @75
    @21
    @10
    cvv
    wcel
    @78
    @10
    wceq
    @21
    @43
    simpl
    @7
    @9
    cdiv
    ovex
    vx
    @20
    @10
    cvv
    @31
    @36
    fvmpt2
    sylancl
    eqeq1d
    @75
    @80
    @5
    @7
    @75
    @43
    @5
    cvv
    wcel
    @80
    @5
    wceq
    @21
    @43
    simpr
    @2
    @4
    cdiv
    ovex
    vy
    @19
    @5
    cvv
    @34
    @52
    fvmpt2
    sylancl
    eqeq1d
    3bitr3rd
    @7
    @5
    eqcom
    @2
    @10
    eqcom
    3bitr4g
    syl2an
    an4s
    anass1rs
    ifbothda
    ifbothda
    adantl
    f1ocnv2d
    trud
end
