include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "wral.mm"
include "elfz1end.mm"
include "biimpi.mm"
include "cv.mm"
include "caddc.mm"
include "wceq.mm"
include "oveq2.mm"
include "raleqdv.mm"
include "weq.mm"
include "wb.mm"
include "elfz1eq.mm"
include "syl.mm"
include "mpbiri.mm"
include "rgen.mm"
include "csn.mm"
include "wa.mm"
include "wsbc.mm"
include "cdvds.mm"
include "wbr.mm"
include "c2.mm"
include "cmin.mm"
include "wrex.mm"
include "cdiv.mm"
include "cmul.mm"
include "peano2nn.mm"
include "ad2antrr.mm"
include "nncnd.mm"
include "cuz.mm"
include "cfv.mm"
include "elfzuz.mm"
include "ad2antrl.mm"
include "eluz2nn.mm"
include "nnne0d.mm"
include "divcan2d.mm"
include "cz.mm"
include "clt.mm"
include "simprr.mm"
include "cc0.mm"
include "wne.mm"
include "nnzd.mm"
include "dvdsval2.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "mulid2d.mm"
include "cle.mm"
include "elfzle2.mm"
include "cc.mm"
include "nncn.mm"
include "ax-1cn.mm"
include "pncan.mm"
include "sylancl.mm"
include "breqtrd.mm"
include "nnz.mm"
include "zleltp1.mm"
include "syl2anc.mm"
include "eqbrtrd.mm"
include "cr.mm"
include "1red.mm"
include "nnred.mm"
include "nngt0d.mm"
include "ltmuldiv.mm"
include "syl112anc.mm"
include "eluz2b1.mm"
include "sylanbrc.mm"
include "fznn.mm"
include "mpbir2and.mm"
include "simplr.mm"
include "rspcv.mm"
include "sylc.mm"
include "nnrpd.mm"
include "rpdivcld.mm"
include "rpgt0d.mm"
include "elnnz.mm"
include "dividd.mm"
include "eluz2b2.mm"
include "simprbi.mm"
include "ltdiv23.mm"
include "syl122anc.mm"
include "mpbird.mm"
include "cbvralv.mm"
include "sylib.mm"
include "vex.mm"
include "sbcie.mm"
include "dfsbcq.mm"
include "syl5bbr.mm"
include "jca.mm"
include "wi.mm"
include "anbi2d.mm"
include "ovex.mm"
include "sbceq1d.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "expcom.mm"
include "vtoclga.mm"
include "syl3c.mm"
include "sbceq1dd.mm"
include "rexlimdvaa.mm"
include "wn.mm"
include "ralnex.mm"
include "cprime.mm"
include "simpl.mm"
include "elnnuz.mm"
include "eluzp1p1.mm"
include "df-2.mm"
include "fveq2i.mm"
include "syl6eleqr.mm"
include "isprm3.mm"
include "baibr.mm"
include "simpr.mm"
include "oveq2d.mm"
include "nfcv.mm"
include "nfv.mm"
include "nfsbc1v.mm"
include "nfim.mm"
include "oveq1.mm"
include "sbceq1a.mm"
include "ex.mm"
include "vtoclgaf.mm"
include "syl5com.mm"
include "sylbid.mm"
include "syl5bir.mm"
include "pm2.61d.mm"
include "ralsnsg.mm"
include "sylibrd.mm"
include "ancld.mm"
include "cun.mm"
include "fzsuc.mm"
include "sylbi.mm"
include "ralunb.mm"
include "syl6bb.mm"
include "nnind.mm"

theorem prmind2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vk: setvar k
  let vn: setvar n
  assume prmind.1: |- ( x = 1 -> ( ph <-> ps ) )
  assume prmind.2: |- ( x = y -> ( ph <-> ch ) )
  assume prmind.3: |- ( x = z -> ( ph <-> th ) )
  assume prmind.4: |- ( x = ( y x. z ) -> ( ph <-> ta ) )
  assume prmind.5: |- ( x = A -> ( ph <-> et ) )
  assume prmind.6: |- ps
  assume prmind2.7: |- ( ( x e. Prime /\ A. y e. ( 1 ... ( x - 1 ) ) ch ) -> ph )
  assume prmind2.8: |- ( ( y e. ( ZZ>= ` 2 ) /\ z e. ( ZZ>= ` 2 ) ) -> ( ( ch /\ th ) -> ta ) )

  disjoint x y
  disjoint A x
  disjoint x z
  disjoint ch x
  disjoint ch z
  disjoint et x
  disjoint ta x
  disjoint th x
  disjoint y z
  disjoint ph y
  disjoint ph z
  disjoint k x
  disjoint k y
  disjoint n x
  disjoint A n
  disjoint k n
  disjoint k z
  disjoint k ph
  disjoint n y
  disjoint n z
  disjoint n ph
  assert |- ( A e. NN -> et )

  proof
    cA
    cn
    wcel
    #
    cA
    c1
    cA
    cfz
    co
    #
    wcel
    #
    wph
    vx
    @1
    wral
    #
    wet
    @0
    @2
    cA
    elfz1end
    biimpi
    wph
    vx
    c1
    vn
    cv
    #
    cfz
    co
    #
    wral
    wph
    vx
    c1
    c1
    cfz
    co
    #
    wral
    wph
    vx
    c1
    vk
    cv
    #
    cfz
    co
    #
    wral
    #
    wph
    vx
    c1
    @7
    c1
    caddc
    co
    #
    cfz
    co
    #
    wral
    #
    @3
    vn
    vk
    cA
    @4
    c1
    wceq
    wph
    vx
    @5
    @6
    @4
    c1
    c1
    cfz
    oveq2
    raleqdv
    vn
    vk
    weq
    wph
    vx
    @5
    @8
    @4
    @7
    c1
    cfz
    oveq2
    raleqdv
    @4
    @10
    wceq
    wph
    vx
    @5
    @11
    @4
    @10
    c1
    cfz
    oveq2
    raleqdv
    @4
    cA
    wceq
    wph
    vx
    @5
    @1
    @4
    cA
    c1
    cfz
    oveq2
    raleqdv
    wph
    vx
    @6
    vx
    cv
    #
    @6
    wcel
    #
    wph
    wps
    prmind.6
    @14
    @13
    c1
    wceq
    wph
    wps
    wb
    @13
    c1
    elfz1eq
    prmind.1
    syl
    mpbiri
    rgen
    @7
    cn
    wcel
    #
    @9
    @9
    wph
    vx
    @10
    csn
    #
    wral
    #
    wa
    #
    @12
    @15
    @9
    @17
    @15
    @9
    wph
    vx
    @10
    wsbc
    #
    @17
    @15
    @9
    @19
    @15
    @9
    wa
    #
    vy
    cv
    #
    @10
    cdvds
    wbr
    #
    vy
    c2
    @10
    c1
    cmin
    co
    #
    cfz
    co
    #
    wrex
    #
    @19
    @20
    @22
    @19
    vy
    @24
    @20
    @21
    @24
    wcel
    #
    @22
    wa
    #
    wa
    #
    wph
    vx
    @21
    @10
    @21
    cdiv
    co
    #
    cmul
    co
    #
    @10
    @28
    @10
    @21
    @28
    @10
    @15
    @10
    cn
    wcel
    #
    @9
    @27
    @7
    peano2nn
    #
    ad2antrr
    #
    nncnd
    #
    @28
    @21
    @28
    @21
    c2
    cuz
    cfv
    #
    wcel
    #
    @21
    cn
    wcel
    #
    @26
    @36
    @20
    @22
    @21
    c2
    @23
    elfzuz
    ad2antrl
    #
    @21
    eluz2nn
    syl
    #
    nncnd
    #
    @28
    @21
    @39
    nnne0d
    #
    divcan2d
    @28
    @29
    @35
    wcel
    #
    @36
    wch
    wph
    vx
    @29
    wsbc
    #
    wa
    #
    wph
    vx
    @30
    wsbc
    #
    @28
    @29
    cz
    wcel
    #
    c1
    @29
    clt
    wbr
    #
    @42
    @28
    @22
    @46
    @20
    @26
    @22
    simprr
    @28
    @21
    cz
    wcel
    #
    @21
    cc0
    wne
    @10
    cz
    wcel
    @22
    @46
    wb
    @28
    @21
    @39
    nnzd
    #
    @41
    @28
    @10
    @33
    nnzd
    @21
    @10
    dvdsval2
    syl3anc
    mpbid
    #
    @28
    c1
    @21
    cmul
    co
    #
    @10
    clt
    wbr
    #
    @47
    @28
    @51
    @21
    @10
    clt
    @28
    @21
    @40
    mulid2d
    @28
    @21
    @7
    cle
    wbr
    #
    @21
    @10
    clt
    wbr
    #
    @28
    @21
    @23
    @7
    cle
    @26
    @21
    @23
    cle
    wbr
    @20
    @22
    @21
    c2
    @23
    elfzle2
    ad2antrl
    @28
    @7
    cc
    wcel
    #
    c1
    cc
    wcel
    #
    @23
    @7
    wceq
    #
    @15
    @55
    @9
    @27
    @7
    nncn
    ad2antrr
    ax-1cn
    @7
    c1
    pncan
    #
    sylancl
    breqtrd
    #
    @28
    @48
    @7
    cz
    wcel
    #
    @53
    @54
    wb
    @49
    @15
    @60
    @9
    @27
    @7
    nnz
    ad2antrr
    #
    @21
    @7
    zleltp1
    syl2anc
    mpbid
    eqbrtrd
    @28
    c1
    cr
    wcel
    @10
    cr
    wcel
    #
    @21
    cr
    wcel
    #
    cc0
    @21
    clt
    wbr
    #
    @52
    @47
    wb
    @28
    1red
    @28
    @10
    @33
    nnred
    #
    @28
    @21
    @39
    nnred
    #
    @28
    @21
    @39
    nngt0d
    #
    c1
    @10
    @21
    ltmuldiv
    syl112anc
    mpbid
    @29
    eluz2b1
    sylanbrc
    @38
    @28
    wch
    @43
    @28
    @21
    @8
    wcel
    #
    @9
    wch
    @28
    @68
    @37
    @53
    @39
    @59
    @28
    @60
    @68
    @37
    @53
    wa
    wb
    @61
    @21
    @7
    fznn
    syl
    mpbir2and
    @15
    @9
    @27
    simplr
    #
    wph
    wch
    vx
    @21
    @8
    prmind.2
    rspcv
    sylc
    @28
    @29
    @8
    wcel
    #
    wth
    vz
    @8
    wral
    #
    @43
    @28
    @70
    @29
    cn
    wcel
    #
    @29
    @7
    cle
    wbr
    #
    @28
    @46
    cc0
    @29
    clt
    wbr
    @72
    @50
    @28
    @29
    @28
    @10
    @21
    @28
    @10
    @33
    nnrpd
    @28
    @21
    @39
    nnrpd
    rpdivcld
    rpgt0d
    @29
    elnnz
    sylanbrc
    @28
    @73
    @29
    @10
    clt
    wbr
    #
    @28
    @10
    @10
    cdiv
    co
    #
    @21
    clt
    wbr
    #
    @74
    @28
    @75
    c1
    @21
    clt
    @28
    @10
    @34
    @28
    @10
    @33
    nnne0d
    dividd
    @28
    @36
    c1
    @21
    clt
    wbr
    #
    @38
    @36
    @37
    @77
    @21
    eluz2b2
    simprbi
    syl
    eqbrtrd
    @28
    @62
    @62
    cc0
    @10
    clt
    wbr
    @63
    @64
    @76
    @74
    wb
    @65
    @65
    @28
    @10
    @33
    nngt0d
    @66
    @67
    @10
    @10
    @21
    ltdiv23
    syl122anc
    mpbid
    @28
    @46
    @60
    @73
    @74
    wb
    @50
    @61
    @29
    @7
    zleltp1
    syl2anc
    mpbird
    @28
    @60
    @70
    @72
    @73
    wa
    wb
    @61
    @29
    @7
    fznn
    syl
    mpbir2and
    @28
    @9
    @71
    @69
    wph
    wth
    vx
    vz
    @8
    prmind.3
    cbvralv
    sylib
    wth
    @43
    vz
    @29
    @8
    wth
    wph
    vx
    vz
    cv
    #
    wsbc
    @78
    @29
    wceq
    #
    @43
    wph
    wth
    vx
    @78
    vz
    vex
    prmind.3
    sbcie
    wph
    vx
    @78
    @29
    dfsbcq
    syl5bbr
    #
    rspcv
    sylc
    jca
    @36
    wch
    wth
    wa
    #
    wta
    wi
    #
    wi
    @36
    @44
    @45
    wi
    #
    wi
    vz
    @29
    @35
    @79
    @82
    @83
    @36
    @79
    @81
    @44
    wta
    @45
    @79
    wth
    @43
    wch
    @80
    anbi2d
    wta
    wph
    vx
    @21
    @78
    cmul
    co
    #
    wsbc
    @79
    @45
    wph
    wta
    vx
    @84
    @21
    @78
    cmul
    ovex
    prmind.4
    sbcie
    @79
    wph
    vx
    @84
    @30
    @78
    @29
    @21
    cmul
    oveq2
    sbceq1d
    syl5bbr
    imbi12d
    imbi2d
    @36
    @78
    @35
    wcel
    @82
    prmind2.8
    expcom
    vtoclga
    syl3c
    sbceq1dd
    rexlimdvaa
    @25
    wn
    @22
    wn
    vy
    @24
    wral
    #
    @20
    @19
    @22
    vy
    @24
    ralnex
    @20
    @85
    @10
    cprime
    wcel
    #
    @19
    @20
    @10
    @35
    wcel
    #
    @85
    @86
    wb
    @20
    @10
    c1
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    @35
    @20
    @7
    c1
    cuz
    cfv
    wcel
    #
    @10
    @89
    wcel
    @20
    @15
    @90
    @15
    @9
    simpl
    #
    @7
    elnnuz
    #
    sylib
    c1
    @7
    eluzp1p1
    syl
    c2
    @88
    cuz
    df-2
    fveq2i
    syl6eleqr
    @86
    @87
    @85
    vy
    @10
    isprm3
    baibr
    syl
    @20
    wch
    vy
    c1
    @23
    cfz
    co
    #
    wral
    #
    @86
    @19
    @20
    @94
    wch
    vy
    @8
    wral
    #
    @20
    @9
    @95
    @15
    @9
    simpr
    wph
    wch
    vx
    vy
    @8
    prmind.2
    cbvralv
    sylib
    @20
    wch
    vy
    @93
    @8
    @20
    @23
    @7
    c1
    cfz
    @20
    @55
    @56
    @57
    @20
    @7
    @91
    nncnd
    ax-1cn
    @58
    sylancl
    oveq2d
    raleqdv
    mpbird
    wch
    vy
    c1
    @13
    c1
    cmin
    co
    #
    cfz
    co
    #
    wral
    #
    wph
    wi
    @94
    @19
    wi
    vx
    @10
    cprime
    vx
    @10
    nfcv
    @94
    @19
    vx
    @94
    vx
    nfv
    wph
    vx
    @10
    nfsbc1v
    nfim
    @13
    @10
    wceq
    #
    @98
    @94
    wph
    @19
    @99
    wch
    vy
    @97
    @93
    @99
    @96
    @23
    c1
    cfz
    @13
    @10
    c1
    cmin
    oveq1
    oveq2d
    raleqdv
    wph
    vx
    @10
    sbceq1a
    imbi12d
    @13
    cprime
    wcel
    @98
    wph
    prmind2.7
    ex
    vtoclgaf
    syl5com
    sylbid
    syl5bir
    pm2.61d
    ex
    @15
    @31
    @17
    @19
    wb
    @32
    wph
    vx
    @10
    cn
    ralsnsg
    syl
    sylibrd
    ancld
    @15
    @12
    wph
    vx
    @8
    @16
    cun
    #
    wral
    @18
    @15
    wph
    vx
    @11
    @100
    @15
    @90
    @11
    @100
    wceq
    @92
    c1
    @7
    fzsuc
    sylbi
    raleqdv
    wph
    vx
    @8
    @16
    ralunb
    syl6bb
    sylibrd
    nnind
    wph
    wet
    vx
    cA
    @1
    prmind.5
    rspcv
    sylc
end
