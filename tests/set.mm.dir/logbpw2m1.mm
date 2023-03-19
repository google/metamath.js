include "cn.mm"
include "wcel.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "clogb.mm"
include "cfl.mm"
include "cfv.mm"
include "cz.mm"
include "cle.mm"
include "wbr.mm"
include "caddc.mm"
include "clt.mm"
include "wceq.mm"
include "crp.mm"
include "wne.mm"
include "cr.mm"
include "2rp.mm"
include "a1i.mm"
include "cn0.mm"
include "2nn0.mm"
include "nnnn0.mm"
include "nn0expcld.mm"
include "nnge1.mm"
include "2re.mm"
include "1zzd.mm"
include "nnz.mm"
include "1lt2.mm"
include "leexp2d.mm"
include "cc.mm"
include "2cn.mm"
include "exp1.mm"
include "ax-mp.mm"
include "breq1d.mm"
include "bitrd.mm"
include "mpbid.mm"
include "nn0ge2m1nn.mm"
include "syl2anc.mm"
include "nnrpd.mm"
include "1ne2.mm"
include "necomi.mm"
include "relogbcl.mm"
include "syl3anc.mm"
include "flcld.mm"
include "peano2zm.mm"
include "syl.mm"
include "cuz.mm"
include "2z.mm"
include "uzid.mm"
include "nnlogbexp.mm"
include "sylancr.mm"
include "fveq2d.mm"
include "flid.mm"
include "eqtrd.mm"
include "2nn.mm"
include "nnm1nn0.mm"
include "nnexpcld.mm"
include "pw2m1lepw2m1.mm"
include "wb.mm"
include "logbleb.mm"
include "flwordi.mm"
include "eqbrtrrd.mm"
include "nnnn0d.mm"
include "zred.mm"
include "nnre.mm"
include "peano2rem.mm"
include "peano2re.mm"
include "flle.mm"
include "nnred.mm"
include "ltm1d.mm"
include "logblt.mm"
include "leidd.mm"
include "nncn.mm"
include "npcan1.mm"
include "3brtr4d.mm"
include "ltletrd.mm"
include "lelttrd.mm"
include "wa.mm"
include "zgeltp1eq.mm"
include "imp.mm"
include "syl22anc.mm"

theorem logbpw2m1
  let cI: class I
  let vk: setvar k
  let vx: setvar x


  assert |- ( I e. NN -> ( |_ ` ( 2 logb ( ( 2 ^ I ) - 1 ) ) ) = ( I - 1 ) )

  proof
    cI
    cn
    wcel
    #
    c2
    c2
    cI
    cexp
    co
    #
    c1
    cmin
    co
    #
    clogb
    co
    #
    cfl
    cfv
    #
    cz
    wcel
    #
    cI
    c1
    cmin
    co
    #
    cz
    wcel
    #
    @6
    @4
    cle
    wbr
    #
    @4
    @6
    c1
    caddc
    co
    #
    clt
    wbr
    #
    @4
    @6
    wceq
    #
    @0
    @3
    @0
    c2
    crp
    wcel
    #
    @2
    crp
    wcel
    #
    c2
    c1
    wne
    #
    @3
    cr
    wcel
    #
    @12
    @0
    2rp
    a1i
    #
    @0
    @2
    @0
    @1
    cn0
    wcel
    #
    c2
    @1
    cle
    wbr
    #
    @2
    cn
    wcel
    #
    @0
    c2
    cI
    c2
    cn0
    wcel
    @0
    2nn0
    a1i
    cI
    nnnn0
    #
    nn0expcld
    @0
    c1
    cI
    cle
    wbr
    #
    @18
    cI
    nnge1
    @0
    @21
    c2
    c1
    cexp
    co
    #
    @1
    cle
    wbr
    @18
    @0
    c2
    c1
    cI
    c2
    cr
    wcel
    @0
    2re
    a1i
    @0
    1zzd
    cI
    nnz
    #
    c1
    c2
    clt
    wbr
    @0
    1lt2
    a1i
    leexp2d
    @0
    @22
    c2
    @1
    cle
    @22
    c2
    wceq
    #
    @0
    c2
    cc
    wcel
    @24
    2cn
    c2
    exp1
    ax-mp
    a1i
    breq1d
    bitrd
    mpbid
    #
    @1
    nn0ge2m1nn
    #
    syl2anc
    nnrpd
    #
    @14
    @0
    c1
    c2
    1ne2
    necomi
    a1i
    #
    c2
    @2
    relogbcl
    #
    syl3anc
    #
    flcld
    @0
    cI
    cz
    wcel
    #
    @7
    @23
    cI
    peano2zm
    syl
    #
    @0
    c2
    c2
    @6
    cexp
    co
    #
    clogb
    co
    #
    cfl
    cfv
    #
    @6
    @4
    cle
    @0
    @35
    @6
    cfl
    cfv
    #
    @6
    @0
    @34
    @6
    cfl
    @0
    c2
    c2
    cuz
    cfv
    wcel
    #
    @7
    @34
    @6
    wceq
    c2
    cz
    wcel
    @37
    2z
    c2
    uzid
    ax-mp
    #
    @32
    c2
    @6
    nnlogbexp
    sylancr
    fveq2d
    @0
    @7
    @36
    @6
    wceq
    @32
    @6
    flid
    syl
    eqtrd
    @0
    @34
    cr
    wcel
    #
    @15
    @34
    @3
    cle
    wbr
    #
    @35
    @4
    cle
    wbr
    @0
    @12
    @33
    crp
    wcel
    #
    @14
    @39
    @16
    @0
    @33
    @0
    c2
    @6
    c2
    cn
    wcel
    @0
    2nn
    a1i
    #
    cI
    nnm1nn0
    nnexpcld
    nnrpd
    #
    @28
    c2
    @33
    relogbcl
    syl3anc
    @30
    @0
    @33
    @2
    cle
    wbr
    #
    @40
    cI
    pw2m1lepw2m1
    @0
    @37
    @41
    @13
    @44
    @40
    wb
    @37
    @0
    @38
    a1i
    #
    @43
    @27
    c2
    @33
    @2
    logbleb
    syl3anc
    mpbid
    @34
    @3
    flwordi
    syl3anc
    eqbrtrrd
    @0
    @4
    @3
    @9
    @0
    @4
    @0
    @3
    @0
    @12
    @13
    @14
    @15
    @16
    @0
    @2
    @0
    @17
    @18
    @19
    @0
    @1
    @0
    c2
    cI
    @42
    @20
    nnexpcld
    #
    nnnn0d
    @25
    @26
    syl2anc
    nnrpd
    @28
    @29
    syl3anc
    flcld
    zred
    @30
    @0
    @6
    cr
    wcel
    #
    @9
    cr
    wcel
    @0
    cI
    cr
    wcel
    @47
    cI
    nnre
    #
    cI
    peano2rem
    syl
    @6
    peano2re
    syl
    #
    @0
    @15
    @4
    @3
    cle
    wbr
    @30
    @3
    flle
    syl
    @0
    @3
    c2
    @1
    clogb
    co
    #
    @9
    @30
    @0
    @12
    @1
    crp
    wcel
    #
    @14
    @50
    cr
    wcel
    @16
    @0
    @1
    @46
    nnrpd
    #
    @28
    c2
    @1
    relogbcl
    syl3anc
    @49
    @0
    @2
    @1
    clt
    wbr
    #
    @3
    @50
    clt
    wbr
    #
    @0
    @1
    @0
    @1
    @46
    nnred
    ltm1d
    @0
    @37
    @13
    @51
    @53
    @54
    wb
    @45
    @27
    @52
    c2
    @2
    @1
    logblt
    syl3anc
    mpbid
    @0
    cI
    cI
    @50
    @9
    cle
    @0
    cI
    @48
    leidd
    @0
    @37
    @31
    @50
    cI
    wceq
    @38
    @23
    c2
    cI
    nnlogbexp
    sylancr
    @0
    cI
    cc
    wcel
    @9
    cI
    wceq
    cI
    nncn
    cI
    npcan1
    syl
    3brtr4d
    ltletrd
    lelttrd
    @5
    @7
    wa
    @8
    @10
    wa
    @11
    @6
    @4
    zgeltp1eq
    imp
    syl22anc
end
