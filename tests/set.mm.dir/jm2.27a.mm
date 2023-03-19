include "crmy.mm"
include "co.mm"
include "wceq.mm"
include "c2.mm"
include "cmul.mm"
include "cmin.mm"
include "cdvds.mm"
include "wbr.mm"
include "cneg.mm"
include "wo.mm"
include "cz.mm"
include "wcel.mm"
include "2z.mm"
include "nnzd.mm"
include "zmulcl.mm"
include "sylancr.mm"
include "nn0zd.mm"
include "congsym.mm"
include "syl22anc.mm"
include "c1.mm"
include "cuz.mm"
include "cfv.mm"
include "cn0.mm"
include "cc0.mm"
include "cle.mm"
include "nn0ge0d.mm"
include "rmy0.mm"
include "syl.mm"
include "eqcomd.mm"
include "3brtr4d.mm"
include "wb.mm"
include "0zd.mm"
include "lermy.mm"
include "syl3anc.mm"
include "mpbird.mm"
include "elnn0z.mm"
include "sylanbrc.mm"
include "jm2.16nn0.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "breqtrrd.mm"
include "wa.mm"
include "wi.mm"
include "peano2zm.mm"
include "zsubcld.mm"
include "dvdstr.mm"
include "mp2and.mm"
include "congtr.mm"
include "syl222anc.mm"
include "orcd.mm"
include "cexp.mm"
include "caddc.mm"
include "zsqcl.mm"
include "dvdsmul2.mm"
include "peano2zd.mm"
include "dvdsmultr2.mm"
include "mpd.mm"
include "eqtr3d.mm"
include "3brtr3d.mm"
include "cn.mm"
include "clt.mm"
include "zred.mm"
include "nn0p1nn.mm"
include "nngt0d.mm"
include "2nn.mm"
include "nnsqcld.mm"
include "nnmulcl.mm"
include "mulgt0d.mm"
include "ltrmy.mm"
include "elnnz.mm"
include "jm2.20nn.mm"
include "mpbid.mm"
include "eqeltrrd.mm"
include "muldvds2.mm"
include "eqbrtrd.mm"
include "a1i.mm"
include "dvdscmul.mm"
include "crmx.mm"
include "frmy.mm"
include "fovcl.mm"
include "eluzelz.mm"
include "eqbrtrrd.mm"
include "jm2.15nn0.mm"
include "oveq12d.mm"
include "jm2.26.mm"
include "dvdsacongtr.mm"
include "acongtr.mm"
include "cfz.mm"
include "nnnn0d.mm"
include "elfz2nn0.mm"
include "syl3anbrc.mm"
include "rmygeid.mm"
include "acongeq.mm"
include "oveq2d.mm"
include "eqtr4d.mm"

theorem jm2.27a
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cJ: class J
  assume jm2.27a1: |- ( ph -> A e. ( ZZ>= ` 2 ) )
  assume jm2.27a2: |- ( ph -> B e. NN )
  assume jm2.27a3: |- ( ph -> C e. NN )
  assume jm2.27a4: |- ( ph -> D e. NN0 )
  assume jm2.27a5: |- ( ph -> E e. NN0 )
  assume jm2.27a6: |- ( ph -> F e. NN0 )
  assume jm2.27a7: |- ( ph -> G e. NN0 )
  assume jm2.27a8: |- ( ph -> H e. NN0 )
  assume jm2.27a9: |- ( ph -> I e. NN0 )
  assume jm2.27a10: |- ( ph -> J e. NN0 )
  assume jm2.27a11: |- ( ph -> ( ( D ^ 2 ) - ( ( ( A ^ 2 ) - 1 ) x. ( C ^ 2 ) ) ) = 1 )
  assume jm2.27a12: |- ( ph -> ( ( F ^ 2 ) - ( ( ( A ^ 2 ) - 1 ) x. ( E ^ 2 ) ) ) = 1 )
  assume jm2.27a13: |- ( ph -> G e. ( ZZ>= ` 2 ) )
  assume jm2.27a14: |- ( ph -> ( ( I ^ 2 ) - ( ( ( G ^ 2 ) - 1 ) x. ( H ^ 2 ) ) ) = 1 )
  assume jm2.27a15: |- ( ph -> E = ( ( J + 1 ) x. ( 2 x. ( C ^ 2 ) ) ) )
  assume jm2.27a16: |- ( ph -> F || ( G - A ) )
  assume jm2.27a17: |- ( ph -> ( 2 x. C ) || ( G - 1 ) )
  assume jm2.27a18: |- ( ph -> F || ( H - C ) )
  assume jm2.27a19: |- ( ph -> ( 2 x. C ) || ( H - B ) )
  assume jm2.27a20: |- ( ph -> B <_ C )
  assume jm2.27a21: |- ( ph -> P e. ZZ )
  assume jm2.27a22: |- ( ph -> D = ( A rmX P ) )
  assume jm2.27a23: |- ( ph -> C = ( A rmY P ) )
  assume jm2.27a24: |- ( ph -> Q e. ZZ )
  assume jm2.27a25: |- ( ph -> F = ( A rmX Q ) )
  assume jm2.27a26: |- ( ph -> E = ( A rmY Q ) )
  assume jm2.27a27: |- ( ph -> R e. ZZ )
  assume jm2.27a28: |- ( ph -> I = ( G rmX R ) )
  assume jm2.27a29: |- ( ph -> H = ( G rmY R ) )


  assert |- ( ph -> C = ( A rmY B ) )

  proof
    wph
    cC
    cA
    cP
    crmy
    co
    #
    cA
    cB
    crmy
    co
    jm2.27a23
    wph
    cB
    cP
    cA
    crmy
    wph
    cB
    cP
    wceq
    #
    c2
    cC
    cmul
    co
    #
    cB
    cP
    cmin
    co
    cdvds
    wbr
    @2
    cB
    cP
    cneg
    #
    cmin
    co
    cdvds
    wbr
    wo
    #
    wph
    @2
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    cR
    cz
    wcel
    #
    cP
    cz
    wcel
    #
    @2
    cB
    cR
    cmin
    co
    cdvds
    wbr
    #
    @2
    cB
    cR
    cneg
    cmin
    co
    cdvds
    wbr
    #
    wo
    @2
    cR
    cP
    cmin
    co
    #
    cdvds
    wbr
    @2
    cR
    @3
    cmin
    co
    #
    cdvds
    wbr
    wo
    #
    @4
    wph
    c2
    cz
    wcel
    #
    cC
    cz
    wcel
    #
    @5
    2z
    wph
    cC
    jm2.27a3
    nnzd
    #
    c2
    cC
    zmulcl
    sylancr
    #
    wph
    cB
    jm2.27a2
    nnzd
    #
    jm2.27a27
    jm2.27a21
    wph
    @9
    @10
    wph
    @5
    @6
    cH
    cz
    wcel
    #
    @7
    @2
    cB
    cH
    cmin
    co
    cdvds
    wbr
    #
    @2
    cH
    cR
    cmin
    co
    #
    cdvds
    wbr
    #
    @9
    @17
    @18
    wph
    cH
    jm2.27a8
    nn0zd
    #
    jm2.27a27
    wph
    @5
    @19
    @6
    @2
    cH
    cB
    cmin
    co
    cdvds
    wbr
    @20
    @17
    @23
    @18
    jm2.27a19
    @2
    cH
    cB
    congsym
    syl22anc
    wph
    @2
    cG
    c1
    cmin
    co
    #
    cdvds
    wbr
    #
    @24
    @21
    cdvds
    wbr
    #
    @22
    jm2.27a17
    wph
    @24
    cG
    cR
    crmy
    co
    #
    cR
    cmin
    co
    #
    @21
    cdvds
    wph
    cG
    c2
    cuz
    cfv
    #
    wcel
    #
    cR
    cn0
    wcel
    #
    @24
    @28
    cdvds
    wbr
    jm2.27a13
    wph
    @7
    cc0
    cR
    cle
    wbr
    #
    @31
    jm2.27a27
    wph
    @32
    cG
    cc0
    crmy
    co
    #
    @27
    cle
    wbr
    #
    wph
    cc0
    cH
    @33
    @27
    cle
    wph
    cH
    jm2.27a8
    nn0ge0d
    wph
    @30
    @33
    cc0
    wceq
    jm2.27a13
    cG
    rmy0
    syl
    wph
    cH
    @27
    jm2.27a29
    eqcomd
    3brtr4d
    wph
    @30
    cc0
    cz
    wcel
    #
    @7
    @32
    @34
    wb
    jm2.27a13
    wph
    0zd
    #
    jm2.27a27
    cG
    cc0
    cR
    lermy
    syl3anc
    mpbird
    cR
    elnn0z
    sylanbrc
    #
    cG
    cR
    jm2.16nn0
    syl2anc
    wph
    cH
    @27
    cR
    cmin
    jm2.27a29
    oveq1d
    breqtrrd
    wph
    @5
    @24
    cz
    wcel
    #
    @21
    cz
    wcel
    @25
    @26
    wa
    @22
    wi
    @17
    wph
    cG
    cz
    wcel
    #
    @38
    wph
    cG
    jm2.27a7
    nn0zd
    #
    cG
    peano2zm
    syl
    wph
    cH
    cR
    @23
    jm2.27a27
    zsubcld
    @2
    @24
    @21
    dvdstr
    syl3anc
    mp2and
    @2
    cB
    cH
    cR
    congtr
    syl222anc
    orcd
    wph
    c2
    cQ
    cmul
    co
    #
    cz
    wcel
    #
    @7
    @8
    @5
    @2
    @41
    cdvds
    wbr
    #
    @41
    @11
    cdvds
    wbr
    @41
    @12
    cdvds
    wbr
    wo
    #
    @13
    wph
    @14
    cQ
    cz
    wcel
    #
    @42
    2z
    jm2.27a24
    c2
    cQ
    zmulcl
    sylancr
    jm2.27a27
    jm2.27a21
    @17
    wph
    cC
    cQ
    cdvds
    wbr
    #
    @43
    wph
    cC
    @0
    cQ
    cdvds
    jm2.27a23
    wph
    cP
    @0
    cmul
    co
    cQ
    cdvds
    wbr
    #
    @0
    cQ
    cdvds
    wbr
    #
    wph
    @0
    c2
    cexp
    co
    #
    cA
    cQ
    crmy
    co
    #
    cdvds
    wbr
    #
    @47
    wph
    cC
    c2
    cexp
    co
    #
    cJ
    c1
    caddc
    co
    #
    c2
    @52
    cmul
    co
    #
    cmul
    co
    #
    @49
    @50
    cdvds
    wph
    @52
    @54
    cdvds
    wbr
    #
    @52
    @55
    cdvds
    wbr
    #
    wph
    @14
    @52
    cz
    wcel
    #
    @56
    2z
    wph
    @15
    @58
    @16
    cC
    zsqcl
    syl
    #
    c2
    @52
    dvdsmul2
    sylancr
    wph
    @58
    @53
    cz
    wcel
    @54
    cz
    wcel
    #
    @56
    @57
    wi
    @59
    wph
    cJ
    wph
    cJ
    jm2.27a10
    nn0zd
    peano2zd
    #
    wph
    @14
    @58
    @60
    2z
    @59
    c2
    @52
    zmulcl
    sylancr
    #
    @52
    @53
    @54
    dvdsmultr2
    syl3anc
    mpd
    wph
    cC
    @0
    c2
    cexp
    jm2.27a23
    oveq1d
    wph
    cE
    @55
    @50
    jm2.27a15
    jm2.27a26
    eqtr3d
    3brtr3d
    wph
    cA
    @29
    wcel
    #
    cQ
    cn
    wcel
    #
    cP
    cn
    wcel
    #
    @51
    @47
    wb
    jm2.27a1
    wph
    @45
    cc0
    cQ
    clt
    wbr
    #
    @64
    jm2.27a24
    wph
    @66
    cA
    cc0
    crmy
    co
    #
    @50
    clt
    wbr
    #
    wph
    cc0
    cE
    @67
    @50
    clt
    wph
    cc0
    @55
    cE
    clt
    wph
    @53
    @54
    wph
    @53
    @61
    zred
    wph
    @54
    @62
    zred
    wph
    @53
    wph
    cJ
    cn0
    wcel
    @53
    cn
    wcel
    jm2.27a10
    cJ
    nn0p1nn
    syl
    nngt0d
    wph
    @54
    wph
    c2
    cn
    wcel
    @52
    cn
    wcel
    @54
    cn
    wcel
    2nn
    wph
    cC
    jm2.27a3
    nnsqcld
    c2
    @52
    nnmulcl
    sylancr
    nngt0d
    mulgt0d
    jm2.27a15
    breqtrrd
    wph
    @63
    @67
    cc0
    wceq
    jm2.27a1
    cA
    rmy0
    syl
    #
    wph
    cE
    @50
    jm2.27a26
    eqcomd
    3brtr4d
    wph
    @63
    @35
    @45
    @66
    @68
    wb
    jm2.27a1
    @36
    jm2.27a24
    cA
    cc0
    cQ
    ltrmy
    syl3anc
    mpbird
    cQ
    elnnz
    sylanbrc
    #
    wph
    @8
    cc0
    cP
    clt
    wbr
    #
    @65
    jm2.27a21
    wph
    @71
    @67
    @0
    clt
    wbr
    #
    wph
    cc0
    cC
    @67
    @0
    clt
    wph
    cC
    jm2.27a3
    nngt0d
    @69
    wph
    cC
    @0
    jm2.27a23
    eqcomd
    3brtr4d
    wph
    @63
    @35
    @8
    @71
    @72
    wb
    jm2.27a1
    @36
    jm2.27a21
    cA
    cc0
    cP
    ltrmy
    syl3anc
    mpbird
    cP
    elnnz
    sylanbrc
    #
    cA
    cQ
    cP
    jm2.20nn
    syl3anc
    mpbid
    wph
    @8
    @0
    cz
    wcel
    #
    @45
    @47
    @48
    wi
    jm2.27a21
    wph
    cC
    @0
    cz
    jm2.27a23
    @16
    eqeltrrd
    #
    jm2.27a24
    cP
    @0
    cQ
    muldvds2
    syl3anc
    mpd
    eqbrtrd
    wph
    @15
    @45
    @14
    @46
    @43
    wi
    @16
    jm2.27a24
    @14
    wph
    2z
    a1i
    c2
    cC
    cQ
    dvdscmul
    syl3anc
    mpd
    wph
    cA
    cQ
    crmx
    co
    #
    cA
    cR
    crmy
    co
    #
    @0
    cmin
    co
    cdvds
    wbr
    #
    @76
    @77
    @0
    cneg
    cmin
    co
    cdvds
    wbr
    #
    wo
    #
    @44
    wph
    @78
    @79
    wph
    @76
    cz
    wcel
    #
    @77
    cz
    wcel
    #
    @27
    cz
    wcel
    @74
    @76
    @77
    @27
    cmin
    co
    #
    cdvds
    wbr
    #
    @76
    @27
    @0
    cmin
    co
    #
    cdvds
    wbr
    @78
    wph
    cF
    @76
    cz
    jm2.27a25
    wph
    cF
    jm2.27a6
    nn0zd
    #
    eqeltrrd
    #
    wph
    @63
    @7
    @82
    jm2.27a1
    jm2.27a27
    cA
    cR
    cz
    @29
    cz
    crmy
    frmy
    fovcl
    syl2anc
    #
    wph
    cH
    @27
    cz
    jm2.27a29
    @23
    eqeltrrd
    #
    @75
    wph
    @76
    cA
    cG
    cmin
    co
    #
    cdvds
    wbr
    #
    @90
    @83
    cdvds
    wbr
    #
    @84
    wph
    cF
    @76
    @90
    cdvds
    jm2.27a25
    wph
    cF
    cz
    wcel
    @39
    cA
    cz
    wcel
    #
    cF
    cG
    cA
    cmin
    co
    cdvds
    wbr
    cF
    @90
    cdvds
    wbr
    @86
    @40
    wph
    @63
    @93
    jm2.27a1
    c2
    cA
    eluzelz
    syl
    #
    jm2.27a16
    cF
    cG
    cA
    congsym
    syl22anc
    eqbrtrrd
    wph
    @63
    @30
    @31
    @92
    jm2.27a1
    jm2.27a13
    @37
    cA
    cG
    cR
    jm2.15nn0
    syl3anc
    wph
    @81
    @90
    cz
    wcel
    @83
    cz
    wcel
    @91
    @92
    wa
    @84
    wi
    @87
    wph
    cA
    cG
    @94
    @40
    zsubcld
    wph
    @77
    @27
    @88
    @89
    zsubcld
    @76
    @90
    @83
    dvdstr
    syl3anc
    mp2and
    wph
    cF
    cH
    cC
    cmin
    co
    @76
    @85
    cdvds
    jm2.27a18
    jm2.27a25
    wph
    cH
    @27
    cC
    @0
    cmin
    jm2.27a29
    jm2.27a23
    oveq12d
    3brtr3d
    @76
    @77
    @27
    @0
    congtr
    syl222anc
    orcd
    wph
    @63
    @64
    @7
    @8
    @80
    @44
    wb
    jm2.27a1
    @70
    jm2.27a27
    jm2.27a21
    cA
    cR
    cP
    cQ
    jm2.26
    syl22anc
    mpbid
    @41
    cR
    cP
    @2
    dvdsacongtr
    syl222anc
    @2
    cB
    cR
    cP
    acongtr
    syl222anc
    wph
    cC
    cn
    wcel
    cB
    cc0
    cC
    cfz
    co
    #
    wcel
    #
    cP
    @95
    wcel
    #
    @1
    @4
    wb
    jm2.27a3
    wph
    cB
    cn0
    wcel
    cC
    cn0
    wcel
    #
    cB
    cC
    cle
    wbr
    @96
    wph
    cB
    jm2.27a2
    nnnn0d
    wph
    cC
    jm2.27a3
    nnnn0d
    #
    jm2.27a20
    cB
    cC
    elfz2nn0
    syl3anbrc
    wph
    cP
    cn0
    wcel
    #
    @98
    cP
    cC
    cle
    wbr
    @97
    wph
    cP
    @73
    nnnn0d
    #
    @99
    wph
    cP
    @0
    cC
    cle
    wph
    @63
    @100
    cP
    @0
    cle
    wbr
    jm2.27a1
    @101
    cA
    cP
    rmygeid
    syl2anc
    jm2.27a23
    breqtrrd
    cP
    cC
    elfz2nn0
    syl3anbrc
    cC
    cB
    cP
    acongeq
    syl3anc
    mpbird
    oveq2d
    eqtr4d
end
