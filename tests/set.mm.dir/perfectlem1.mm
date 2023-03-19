include "c2.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cexp.mm"
include "cn.mm"
include "wcel.mm"
include "cmin.mm"
include "cdiv.mm"
include "cn0.mm"
include "2nn.mm"
include "nnnn0d.mm"
include "peano2nn0.mm"
include "syl.mm"
include "nnexpcl.mm"
include "sylancr.mm"
include "clt.mm"
include "wbr.mm"
include "cr.mm"
include "2re.mm"
include "a1i.mm"
include "peano2nnd.mm"
include "1lt2.mm"
include "expgt1.mm"
include "syl3anc.mm"
include "wb.mm"
include "1nn.mm"
include "nnsub.mm"
include "mpbid.mm"
include "cdvds.mm"
include "cmul.mm"
include "cgcd.mm"
include "wceq.mm"
include "csgm.mm"
include "cz.mm"
include "nnzd.mm"
include "peano2zm.mm"
include "1nn0.mm"
include "sgmnncl.mm"
include "dvdsmul1.mm"
include "syl2anc.mm"
include "cc.mm"
include "2cn.mm"
include "expp1.mm"
include "nncnd.mm"
include "mulcom.mm"
include "sylancl.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "mulassd.mm"
include "ax-1cn.mm"
include "wn.mm"
include "cprime.mm"
include "2prm.mm"
include "coprm.mm"
include "wi.mm"
include "2z.mm"
include "rpexp1i.mm"
include "mpd.mm"
include "sgmmul.mm"
include "syl13anc.mm"
include "pncan.mm"
include "oveq2d.mm"
include "1sgm2ppw.mm"
include "eqtr3d.mm"
include "3eqtr3d.mm"
include "3eqtrd.mm"
include "breqtrrd.mm"
include "gcdcom.mm"
include "iddvdsexp.mm"
include "wa.mm"
include "n2dvds1.mm"
include "w3a.mm"
include "1zzd.mm"
include "3jca.mm"
include "dvdssub2.mm"
include "sylan.mm"
include "mtbiri.mm"
include "ex.mm"
include "mt2d.mm"
include "coprmdvds.mm"
include "mp2and.mm"
include "nndivdvds.mm"

theorem perfectlem1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  assume perfectlem.1: |- ( ph -> A e. NN )
  assume perfectlem.2: |- ( ph -> B e. NN )
  assume perfectlem.3: |- ( ph -> -. 2 || B )
  assume perfectlem.4: |- ( ph -> ( 1 sigma ( ( 2 ^ A ) x. B ) ) = ( 2 x. ( ( 2 ^ A ) x. B ) ) )


  assert |- ( ph -> ( ( 2 ^ ( A + 1 ) ) e. NN /\ ( ( 2 ^ ( A + 1 ) ) - 1 ) e. NN /\ ( B / ( ( 2 ^ ( A + 1 ) ) - 1 ) ) e. NN ) )

  proof
    wph
    c2
    cA
    c1
    caddc
    co
    #
    cexp
    co
    #
    cn
    wcel
    #
    @1
    c1
    cmin
    co
    #
    cn
    wcel
    #
    cB
    @3
    cdiv
    co
    cn
    wcel
    #
    wph
    c2
    cn
    wcel
    #
    @0
    cn0
    wcel
    #
    @2
    2nn
    wph
    cA
    cn0
    wcel
    #
    @7
    wph
    cA
    perfectlem.1
    nnnn0d
    #
    cA
    peano2nn0
    syl
    #
    c2
    @0
    nnexpcl
    sylancr
    #
    wph
    c1
    @1
    clt
    wbr
    #
    @4
    wph
    c2
    cr
    wcel
    #
    @0
    cn
    wcel
    #
    c1
    c2
    clt
    wbr
    #
    @12
    @13
    wph
    2re
    a1i
    wph
    cA
    perfectlem.1
    peano2nnd
    #
    @15
    wph
    1lt2
    a1i
    c2
    @0
    expgt1
    syl3anc
    wph
    c1
    cn
    wcel
    @2
    @12
    @4
    wb
    1nn
    @11
    c1
    @1
    nnsub
    sylancr
    mpbid
    #
    wph
    @3
    cB
    cdvds
    wbr
    #
    @5
    wph
    @3
    @1
    cB
    cmul
    co
    #
    cdvds
    wbr
    #
    @3
    @1
    cgcd
    co
    #
    c1
    wceq
    #
    @18
    wph
    @3
    @3
    c1
    cB
    csgm
    co
    #
    cmul
    co
    #
    @19
    cdvds
    wph
    @3
    cz
    wcel
    #
    @23
    cz
    wcel
    @3
    @24
    cdvds
    wbr
    wph
    @1
    cz
    wcel
    #
    @25
    wph
    @1
    @11
    nnzd
    #
    @1
    peano2zm
    syl
    #
    wph
    @23
    wph
    c1
    cn0
    wcel
    cB
    cn
    wcel
    #
    @23
    cn
    wcel
    1nn0
    perfectlem.2
    c1
    cB
    sgmnncl
    sylancr
    nnzd
    @3
    @23
    dvdsmul1
    syl2anc
    wph
    @19
    c2
    c2
    cA
    cexp
    co
    #
    cmul
    co
    #
    cB
    cmul
    co
    c2
    @30
    cB
    cmul
    co
    #
    cmul
    co
    #
    @24
    wph
    @1
    @31
    cB
    cmul
    wph
    @1
    @30
    c2
    cmul
    co
    #
    @31
    wph
    c2
    cc
    wcel
    #
    @8
    @1
    @34
    wceq
    2cn
    @9
    c2
    cA
    expp1
    sylancr
    wph
    @30
    cc
    wcel
    @35
    @34
    @31
    wceq
    wph
    @30
    wph
    @6
    @8
    @30
    cn
    wcel
    #
    2nn
    @9
    c2
    cA
    nnexpcl
    sylancr
    #
    nncnd
    #
    2cn
    @30
    c2
    mulcom
    sylancl
    eqtrd
    oveq1d
    wph
    c2
    @30
    cB
    @35
    wph
    2cn
    a1i
    @38
    wph
    cB
    perfectlem.2
    nncnd
    mulassd
    wph
    c1
    @32
    csgm
    co
    #
    c1
    @30
    csgm
    co
    #
    @23
    cmul
    co
    #
    @33
    @24
    wph
    c1
    cc
    wcel
    #
    @36
    @29
    @30
    cB
    cgcd
    co
    c1
    wceq
    #
    @39
    @41
    wceq
    @42
    wph
    ax-1cn
    a1i
    @37
    perfectlem.2
    wph
    c2
    cB
    cgcd
    co
    c1
    wceq
    #
    @43
    wph
    c2
    cB
    cdvds
    wbr
    wn
    #
    @44
    perfectlem.3
    wph
    c2
    cprime
    wcel
    #
    cB
    cz
    wcel
    #
    @45
    @44
    wb
    2prm
    wph
    cB
    perfectlem.2
    nnzd
    #
    c2
    cB
    coprm
    sylancr
    mpbid
    wph
    c2
    cz
    wcel
    #
    @47
    @8
    @44
    @43
    wi
    @49
    wph
    2z
    a1i
    #
    @48
    @9
    c2
    cB
    cA
    rpexp1i
    syl3anc
    mpd
    c1
    @30
    cB
    sgmmul
    syl13anc
    perfectlem.4
    wph
    @40
    @3
    @23
    cmul
    wph
    c1
    c2
    @0
    c1
    cmin
    co
    #
    cexp
    co
    #
    csgm
    co
    #
    @40
    @3
    wph
    @52
    @30
    c1
    csgm
    wph
    @51
    cA
    c2
    cexp
    wph
    cA
    cc
    wcel
    @42
    @51
    cA
    wceq
    wph
    cA
    perfectlem.1
    nncnd
    ax-1cn
    cA
    c1
    pncan
    sylancl
    oveq2d
    oveq2d
    wph
    @14
    @53
    @3
    wceq
    @16
    @0
    1sgm2ppw
    syl
    eqtr3d
    oveq1d
    3eqtr3d
    3eqtrd
    breqtrrd
    wph
    @21
    @1
    @3
    cgcd
    co
    #
    c1
    wph
    @25
    @26
    @21
    @54
    wceq
    @28
    @27
    @3
    @1
    gcdcom
    syl2anc
    wph
    c2
    @3
    cgcd
    co
    c1
    wceq
    #
    @54
    c1
    wceq
    #
    wph
    c2
    @3
    cdvds
    wbr
    #
    wn
    #
    @55
    wph
    @57
    c2
    @1
    cdvds
    wbr
    #
    wph
    @49
    @14
    @59
    2z
    @16
    c2
    @0
    iddvdsexp
    sylancr
    wph
    @57
    @59
    wn
    wph
    @57
    wa
    @59
    c2
    c1
    cdvds
    wbr
    #
    n2dvds1
    wph
    @49
    @26
    c1
    cz
    wcel
    #
    w3a
    @57
    @59
    @60
    wb
    wph
    @49
    @26
    @61
    @50
    @27
    wph
    1zzd
    3jca
    c2
    @1
    c1
    dvdssub2
    sylan
    mtbiri
    ex
    mt2d
    wph
    @46
    @25
    @58
    @55
    wb
    2prm
    @28
    c2
    @3
    coprm
    sylancr
    mpbid
    wph
    @49
    @25
    @7
    @55
    @56
    wi
    @50
    @28
    @10
    c2
    @3
    @0
    rpexp1i
    syl3anc
    mpd
    eqtrd
    wph
    @25
    @26
    @47
    @20
    @22
    wa
    @18
    wi
    @28
    @27
    @48
    @3
    @1
    cB
    coprmdvds
    syl3anc
    mp2and
    wph
    @29
    @4
    @18
    @5
    wb
    perfectlem.2
    @17
    cB
    @3
    nndivdvds
    syl2anc
    mpbid
    3jca
end
