include "cn.mm"
include "wcel.mm"
include "c2.mm"
include "cblen.mm"
include "cfv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cexp.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "clogb.mm"
include "cfl.mm"
include "ccxp.mm"
include "caddc.mm"
include "cc.mm"
include "wceq.mm"
include "crp.mm"
include "wne.mm"
include "cr.mm"
include "2rp.mm"
include "a1i.mm"
include "nnrp.mm"
include "1ne2.mm"
include "necomi.mm"
include "relogbcl.mm"
include "syl3anc.mm"
include "flcld.mm"
include "zcnd.mm"
include "pncan1.mm"
include "syl.mm"
include "oveq2d.mm"
include "blennn.mm"
include "oveq1d.mm"
include "2cnd.mm"
include "cc0.mm"
include "2ne0.mm"
include "cxpexpzd.mm"
include "3eqtr4d.mm"
include "flle.mm"
include "2re.mm"
include "1lt2.mm"
include "zred.mm"
include "cxpled.mm"
include "mpbid.mm"
include "cpr.mm"
include "cdif.mm"
include "csn.mm"
include "2cn.mm"
include "eldifpr.mm"
include "mpbir3an.mm"
include "nncn.mm"
include "nnne0.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "cxplogb.mm"
include "sylancr.mm"
include "breqtrd.mm"
include "eqbrtrd.mm"
include "flltp1.mm"
include "peano2zd.mm"
include "cxpltd.mm"
include "3brtr3d.mm"
include "breqtrrd.mm"
include "jca.mm"

theorem nnpw2blen
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( N e. NN -> ( ( 2 ^ ( ( #b ` N ) - 1 ) ) <_ N /\ N < ( 2 ^ ( #b ` N ) ) ) )

  proof
    cN
    cn
    wcel
    #
    c2
    cN
    cblen
    cfv
    #
    c1
    cmin
    co
    #
    cexp
    co
    #
    cN
    cle
    wbr
    cN
    c2
    @1
    cexp
    co
    #
    clt
    wbr
    @0
    @3
    c2
    c2
    cN
    clogb
    co
    #
    cfl
    cfv
    #
    ccxp
    co
    #
    cN
    cle
    @0
    c2
    @6
    c1
    caddc
    co
    #
    c1
    cmin
    co
    #
    cexp
    co
    c2
    @6
    cexp
    co
    @3
    @7
    @0
    @9
    @6
    c2
    cexp
    @0
    @6
    cc
    wcel
    @9
    @6
    wceq
    @0
    @6
    @0
    @5
    @0
    c2
    crp
    wcel
    #
    cN
    crp
    wcel
    c2
    c1
    wne
    #
    @5
    cr
    wcel
    #
    @10
    @0
    2rp
    a1i
    cN
    nnrp
    @11
    @0
    c1
    c2
    1ne2
    necomi
    #
    a1i
    c2
    cN
    relogbcl
    syl3anc
    #
    flcld
    #
    zcnd
    @6
    pncan1
    syl
    oveq2d
    @0
    @2
    @9
    c2
    cexp
    @0
    @1
    @8
    c1
    cmin
    cN
    blennn
    #
    oveq1d
    oveq2d
    @0
    c2
    @6
    @0
    2cnd
    #
    c2
    cc0
    wne
    #
    @0
    2ne0
    a1i
    #
    @15
    cxpexpzd
    3eqtr4d
    @0
    @7
    c2
    @5
    ccxp
    co
    #
    cN
    cle
    @0
    @6
    @5
    cle
    wbr
    #
    @7
    @20
    cle
    wbr
    @0
    @12
    @21
    @14
    @5
    flle
    syl
    @0
    c2
    @6
    @5
    c2
    cr
    wcel
    @0
    2re
    a1i
    #
    c1
    c2
    clt
    wbr
    @0
    1lt2
    a1i
    #
    @0
    @6
    @15
    zred
    @14
    cxpled
    mpbid
    @0
    c2
    cc
    cc0
    c1
    cpr
    cdif
    wcel
    #
    cN
    cc
    cc0
    csn
    cdif
    wcel
    #
    @20
    cN
    wceq
    @24
    c2
    cc
    wcel
    @18
    @11
    2cn
    2ne0
    @13
    c2
    cc
    cc0
    c1
    eldifpr
    mpbir3an
    @0
    cN
    cc
    wcel
    cN
    cc0
    wne
    @25
    cN
    nncn
    cN
    nnne0
    cN
    cc
    cc0
    eldifsn
    sylanbrc
    c2
    cN
    cxplogb
    sylancr
    #
    breqtrd
    eqbrtrd
    @0
    cN
    c2
    @8
    cexp
    co
    #
    @4
    clt
    @0
    @20
    c2
    @8
    ccxp
    co
    #
    cN
    @27
    clt
    @0
    @5
    @8
    clt
    wbr
    #
    @20
    @28
    clt
    wbr
    @0
    @12
    @29
    @14
    @5
    flltp1
    syl
    @0
    c2
    @5
    @8
    @22
    @23
    @14
    @0
    @8
    @0
    @6
    @15
    peano2zd
    #
    zred
    cxpltd
    mpbid
    @26
    @0
    c2
    @8
    @17
    @19
    @30
    cxpexpzd
    3brtr3d
    @0
    @1
    @8
    c2
    cexp
    @16
    oveq2d
    breqtrrd
    jca
end
