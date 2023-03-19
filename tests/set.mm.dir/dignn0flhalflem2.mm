include "cz.mm"
include "wcel.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "cn.mm"
include "cn0.mm"
include "w3a.mm"
include "cfl.mm"
include "cfv.mm"
include "cexp.mm"
include "caddc.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "wceq.mm"
include "cr.mm"
include "zre.mm"
include "rehalfcld.mm"
include "flcld.mm"
include "zred.mm"
include "3ad2ant1.mm"
include "2re.mm"
include "a1i.mm"
include "id.mm"
include "reexpcld.mm"
include "3ad2ant3.mm"
include "2cnd.mm"
include "cc0.mm"
include "wne.mm"
include "2ne0.mm"
include "nn0z.mm"
include "expne0d.mm"
include "redivcld.mm"
include "simp3.mm"
include "1nn0.mm"
include "nn0addcld.mm"
include "peano2zd.mm"
include "nn0p1nn.mm"
include "dignn0flhalflem1.mm"
include "syl3an3.mm"
include "1zzd.mm"
include "flsubz.mm"
include "syl2anc.mm"
include "eqcomd.mm"
include "nnz.mm"
include "zob.mm"
include "syl5ibr.mm"
include "imp.mm"
include "zofldiv2.mm"
include "syldan.mm"
include "3adant3.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "cmul.mm"
include "cc.mm"
include "wa.mm"
include "zcn.mm"
include "1cnd.mm"
include "subcld.mm"
include "crp.mm"
include "2rp.mm"
include "rpcnne0d.mm"
include "rpexpcld.mm"
include "divdiv1.mm"
include "syl3an.mm"
include "recnd.mm"
include "mulcomd.mm"
include "expp1d.mm"
include "eqtr4d.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "3brtr4d.mm"
include "reflcl.mm"
include "syl.mm"
include "flle.mm"
include "lediv1dd.mm"
include "flwordi.mm"
include "syl3anc.mm"
include "rpcnd.mm"
include "expp1zd.mm"
include "breqtrrd.mm"
include "zgtp1leeq.mm"
include "syl22anc.mm"

theorem dignn0flhalflem2
  let cA: class A
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. ZZ /\ ( ( A - 1 ) / 2 ) e. NN /\ N e. NN0 ) -> ( |_ ` ( A / ( 2 ^ ( N + 1 ) ) ) ) = ( |_ ` ( ( |_ ` ( A / 2 ) ) / ( 2 ^ N ) ) ) )

  proof
    cA
    cz
    wcel
    #
    cA
    c1
    cmin
    co
    #
    c2
    cdiv
    co
    #
    cn
    wcel
    #
    cN
    cn0
    wcel
    #
    w3a
    #
    cA
    c2
    cdiv
    co
    #
    cfl
    cfv
    #
    c2
    cN
    cexp
    co
    #
    cdiv
    co
    #
    cfl
    cfv
    #
    cA
    c2
    cN
    c1
    caddc
    co
    #
    cexp
    co
    #
    cdiv
    co
    #
    cfl
    cfv
    #
    @5
    @10
    cz
    wcel
    #
    @14
    cz
    wcel
    #
    @14
    c1
    cmin
    co
    #
    @10
    clt
    wbr
    #
    @10
    @14
    cle
    wbr
    #
    @10
    @14
    wceq
    #
    @5
    @9
    @5
    @7
    @8
    @0
    @3
    @7
    cr
    wcel
    #
    @4
    @0
    @7
    @0
    @6
    @0
    cA
    cA
    zre
    #
    rehalfcld
    flcld
    zred
    3ad2ant1
    @4
    @0
    @8
    cr
    wcel
    @3
    @4
    c2
    cN
    c2
    cr
    wcel
    #
    @4
    2re
    a1i
    @4
    id
    reexpcld
    3ad2ant3
    #
    @5
    c2
    cN
    @5
    2cnd
    #
    c2
    cc0
    wne
    #
    @5
    2ne0
    a1i
    #
    @4
    @0
    cN
    cz
    wcel
    @3
    cN
    nn0z
    #
    3ad2ant3
    #
    expne0d
    #
    redivcld
    #
    flcld
    @5
    @13
    @5
    cA
    @12
    @0
    @3
    cA
    cr
    wcel
    @4
    @22
    3ad2ant1
    #
    @5
    c2
    @11
    @23
    @5
    2re
    a1i
    @5
    cN
    c1
    @0
    @3
    @4
    simp3
    #
    c1
    cn0
    wcel
    @5
    1nn0
    a1i
    nn0addcld
    reexpcld
    @5
    c2
    @11
    @25
    @27
    @5
    cN
    @29
    peano2zd
    expne0d
    redivcld
    #
    flcld
    @5
    @13
    c1
    cmin
    co
    cfl
    cfv
    #
    @1
    @12
    cdiv
    co
    #
    cfl
    cfv
    #
    @17
    @10
    clt
    @4
    @0
    @3
    @11
    cn
    wcel
    @35
    @37
    clt
    wbr
    cN
    nn0p1nn
    cA
    @11
    dignn0flhalflem1
    syl3an3
    @5
    @35
    @17
    @5
    @13
    cr
    wcel
    c1
    cz
    wcel
    @35
    @17
    wceq
    @34
    @5
    1zzd
    @13
    c1
    flsubz
    syl2anc
    eqcomd
    @5
    @10
    @2
    @8
    cdiv
    co
    #
    cfl
    cfv
    @37
    @5
    @9
    @38
    cfl
    @5
    @7
    @2
    @8
    cdiv
    @0
    @3
    @7
    @2
    wceq
    #
    @4
    @0
    @3
    cA
    c1
    caddc
    co
    c2
    cdiv
    co
    cz
    wcel
    #
    @39
    @0
    @3
    @40
    @3
    @40
    @0
    @2
    cz
    wcel
    @2
    nnz
    cA
    zob
    syl5ibr
    imp
    cA
    zofldiv2
    syldan
    3adant3
    oveq1d
    fveq2d
    @5
    @38
    @36
    cfl
    @5
    @38
    @1
    c2
    @8
    cmul
    co
    #
    cdiv
    co
    #
    @36
    @0
    @1
    cc
    wcel
    @3
    c2
    cc
    wcel
    @26
    wa
    #
    @4
    @8
    cc
    wcel
    #
    @8
    cc0
    wne
    wa
    #
    @38
    @42
    wceq
    @0
    cA
    c1
    cA
    zcn
    #
    @0
    1cnd
    subcld
    @3
    c2
    c2
    crp
    wcel
    #
    @3
    2rp
    a1i
    rpcnne0d
    #
    @4
    @8
    @4
    c2
    cN
    @47
    @4
    2rp
    a1i
    @28
    rpexpcld
    #
    rpcnne0d
    #
    @1
    c2
    @8
    divdiv1
    syl3an
    @5
    @41
    @12
    @1
    cdiv
    @5
    @41
    @8
    c2
    cmul
    co
    #
    @12
    @5
    c2
    @8
    @25
    @5
    @8
    @24
    recnd
    mulcomd
    @5
    c2
    cN
    @25
    @33
    expp1d
    eqtr4d
    oveq2d
    eqtrd
    fveq2d
    eqtrd
    3brtr4d
    @5
    @10
    @6
    @8
    cdiv
    co
    #
    cfl
    cfv
    #
    @14
    cle
    @5
    @9
    cr
    wcel
    @52
    cr
    wcel
    @9
    @52
    cle
    wbr
    @10
    @53
    cle
    wbr
    @31
    @5
    @6
    @8
    @5
    cA
    @32
    rehalfcld
    #
    @24
    @30
    redivcld
    @5
    @7
    @6
    @8
    @5
    @6
    cr
    wcel
    #
    @21
    @54
    @6
    reflcl
    syl
    @54
    @5
    c2
    cN
    @47
    @5
    2rp
    a1i
    @29
    rpexpcld
    @5
    @55
    @7
    @6
    cle
    wbr
    @54
    @6
    flle
    syl
    lediv1dd
    @9
    @52
    flwordi
    syl3anc
    @5
    @13
    @52
    cfl
    @5
    @52
    @13
    @5
    @52
    cA
    @41
    cdiv
    co
    #
    @13
    @0
    cA
    cc
    wcel
    @3
    @43
    @4
    @45
    @52
    @56
    wceq
    @46
    @48
    @50
    cA
    c2
    @8
    divdiv1
    syl3an
    @5
    @41
    @12
    cA
    cdiv
    @5
    @41
    @51
    @12
    @5
    c2
    @8
    @25
    @4
    @0
    @44
    @3
    @4
    @8
    @49
    rpcnd
    3ad2ant3
    mulcomd
    @5
    c2
    cN
    @25
    @27
    @29
    expp1zd
    eqtr4d
    oveq2d
    eqtrd
    eqcomd
    fveq2d
    breqtrrd
    @15
    @16
    wa
    @18
    @19
    wa
    @20
    @14
    @10
    zgtp1leeq
    imp
    syl22anc
    eqcomd
end
