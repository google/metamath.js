include "cn.mm"
include "wcel.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cprime.mm"
include "w3a.mm"
include "cfa.mm"
include "cfv.mm"
include "cmin.mm"
include "cmul.mm"
include "cdiv.mm"
include "cpc.mm"
include "cbc.mm"
include "c1.mm"
include "cv.mm"
include "cexp.mm"
include "cfl.mm"
include "caddc.mm"
include "csu.mm"
include "cz.mm"
include "wne.mm"
include "wceq.mm"
include "simp3.mm"
include "cn0.mm"
include "nnnn0.mm"
include "3ad2ant1.mm"
include "faccl.mm"
include "syl.mm"
include "nnzd.mm"
include "nnne0d.mm"
include "fznn0sub.mm"
include "3ad2ant2.mm"
include "elfznn0.mm"
include "nnmulcld.mm"
include "pcdiv.mm"
include "syl121anc.mm"
include "bcval2.mm"
include "oveq2d.mm"
include "fzfid.mm"
include "wa.mm"
include "cr.mm"
include "nnre.mm"
include "adantr.mm"
include "simpl3.mm"
include "prmnn.mm"
include "elfznn.mm"
include "nnnn0d.mm"
include "adantl.mm"
include "nnexpcld.mm"
include "nndivred.mm"
include "flcld.mm"
include "zcnd.mm"
include "nn0red.mm"
include "resubcld.mm"
include "addcld.mm"
include "fsumsub.mm"
include "cuz.mm"
include "nn0zd.mm"
include "uzid.mm"
include "pcfac.mm"
include "syl3anc.mm"
include "cle.mm"
include "wbr.mm"
include "nn0ge0d.mm"
include "subge02d.mm"
include "mpbid.mm"
include "wb.mm"
include "zsubcld.mm"
include "eluz.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "elfzuz3.mm"
include "oveq12d.mm"
include "pcmul.mm"
include "syl122anc.mm"
include "fsumadd.mm"
include "3eqtr4d.mm"
include "eqtr4d.mm"

theorem pcbc
  let cP: class P
  let vk: setvar k
  let cK: class K
  let cN: class N
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let cM: class M

  disjoint P k
  disjoint N k
  disjoint K k
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint m n
  disjoint m x
  disjoint P m
  disjoint n x
  disjoint P n
  disjoint P x
  disjoint N m
  disjoint N x
  disjoint M k
  disjoint M m
  assert |- ( ( N e. NN /\ K e. ( 0 ... N ) /\ P e. Prime ) -> ( P pCnt ( N _C K ) ) = sum_ k e. ( 1 ... N ) ( ( |_ ` ( N / ( P ^ k ) ) ) - ( ( |_ ` ( ( N - K ) / ( P ^ k ) ) ) + ( |_ ` ( K / ( P ^ k ) ) ) ) ) )

  proof
    cN
    cn
    wcel
    #
    cK
    cc0
    cN
    cfz
    co
    wcel
    #
    cP
    cprime
    wcel
    #
    w3a
    #
    cP
    cN
    cfa
    cfv
    #
    cN
    cK
    cmin
    co
    #
    cfa
    cfv
    #
    cK
    cfa
    cfv
    #
    cmul
    co
    #
    cdiv
    co
    #
    cpc
    co
    #
    cP
    @4
    cpc
    co
    #
    cP
    @8
    cpc
    co
    #
    cmin
    co
    #
    cP
    cN
    cK
    cbc
    co
    #
    cpc
    co
    c1
    cN
    cfz
    co
    #
    cN
    cP
    vk
    cv
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
    @17
    cdiv
    co
    #
    cfl
    cfv
    #
    cK
    @17
    cdiv
    co
    #
    cfl
    cfv
    #
    caddc
    co
    #
    cmin
    co
    vk
    csu
    #
    @3
    @2
    @4
    cz
    wcel
    @4
    cc0
    wne
    @8
    cn
    wcel
    @10
    @13
    wceq
    @0
    @1
    @2
    simp3
    #
    @3
    @4
    @3
    cN
    cn0
    wcel
    #
    @4
    cn
    wcel
    @0
    @1
    @27
    @2
    cN
    nnnn0
    3ad2ant1
    #
    cN
    faccl
    syl
    #
    nnzd
    @3
    @4
    @29
    nnne0d
    @3
    @6
    @7
    @3
    @5
    cn0
    wcel
    #
    @6
    cn
    wcel
    @1
    @0
    @30
    @2
    cK
    cc0
    cN
    fznn0sub
    3ad2ant2
    #
    @5
    faccl
    syl
    #
    @3
    cK
    cn0
    wcel
    #
    @7
    cn
    wcel
    @1
    @0
    @33
    @2
    cK
    cN
    elfznn0
    3ad2ant2
    #
    cK
    faccl
    syl
    #
    nnmulcld
    @4
    @8
    cP
    pcdiv
    syl121anc
    @3
    @14
    @9
    cP
    cpc
    @1
    @0
    @14
    @9
    wceq
    @2
    cK
    cN
    bcval2
    3ad2ant2
    oveq2d
    @3
    @25
    @15
    @19
    vk
    csu
    #
    @15
    @24
    vk
    csu
    #
    cmin
    co
    @13
    @3
    @15
    @19
    @24
    vk
    @3
    c1
    cN
    fzfid
    #
    @3
    @16
    @15
    wcel
    #
    wa
    #
    @19
    @40
    @18
    @40
    cN
    @17
    @3
    cN
    cr
    wcel
    #
    @39
    @0
    @1
    @41
    @2
    cN
    nnre
    3ad2ant1
    #
    adantr
    @40
    cP
    @16
    @40
    @2
    cP
    cn
    wcel
    @0
    @1
    @2
    @39
    simpl3
    cP
    prmnn
    syl
    @39
    @16
    cn0
    wcel
    @3
    @39
    @16
    @16
    cN
    elfznn
    nnnn0d
    adantl
    nnexpcld
    #
    nndivred
    flcld
    zcnd
    @40
    @21
    @23
    @40
    @21
    @40
    @20
    @40
    @5
    @17
    @3
    @5
    cr
    wcel
    @39
    @3
    cN
    cK
    @42
    @3
    cK
    @34
    nn0red
    #
    resubcld
    adantr
    @43
    nndivred
    flcld
    zcnd
    #
    @40
    @23
    @40
    @22
    @40
    cK
    @17
    @3
    cK
    cr
    wcel
    @39
    @44
    adantr
    @43
    nndivred
    flcld
    zcnd
    #
    addcld
    fsumsub
    @3
    @11
    @36
    @12
    @37
    cmin
    @3
    @27
    cN
    cN
    cuz
    cfv
    wcel
    #
    @2
    @11
    @36
    wceq
    @28
    @3
    cN
    cz
    wcel
    #
    @47
    @3
    cN
    @28
    nn0zd
    #
    cN
    uzid
    syl
    @26
    cP
    vk
    cN
    cN
    pcfac
    syl3anc
    @3
    cP
    @6
    cpc
    co
    #
    cP
    @7
    cpc
    co
    #
    caddc
    co
    #
    @15
    @21
    vk
    csu
    #
    @15
    @23
    vk
    csu
    #
    caddc
    co
    @12
    @37
    @3
    @50
    @53
    @51
    @54
    caddc
    @3
    @30
    cN
    @5
    cuz
    cfv
    wcel
    #
    @2
    @50
    @53
    wceq
    @31
    @3
    @55
    @5
    cN
    cle
    wbr
    #
    @3
    cc0
    cK
    cle
    wbr
    @56
    @3
    cK
    @34
    nn0ge0d
    @3
    cN
    cK
    @42
    @44
    subge02d
    mpbid
    @3
    @5
    cz
    wcel
    @48
    @55
    @56
    wb
    @3
    cN
    cK
    @49
    @3
    cK
    @34
    nn0zd
    zsubcld
    @49
    @5
    cN
    eluz
    syl2anc
    mpbird
    @26
    cP
    vk
    cN
    @5
    pcfac
    syl3anc
    @3
    @33
    cN
    cK
    cuz
    cfv
    wcel
    #
    @2
    @51
    @54
    wceq
    @34
    @1
    @0
    @57
    @2
    cK
    cc0
    cN
    elfzuz3
    3ad2ant2
    @26
    cP
    vk
    cN
    cK
    pcfac
    syl3anc
    oveq12d
    @3
    @2
    @6
    cz
    wcel
    @6
    cc0
    wne
    @7
    cz
    wcel
    @7
    cc0
    wne
    @12
    @52
    wceq
    @26
    @3
    @6
    @32
    nnzd
    @3
    @6
    @32
    nnne0d
    @3
    @7
    @35
    nnzd
    @3
    @7
    @35
    nnne0d
    @6
    @7
    cP
    pcmul
    syl122anc
    @3
    @15
    @21
    @23
    vk
    @38
    @45
    @46
    fsumadd
    3eqtr4d
    oveq12d
    eqtr4d
    3eqtr4d
end
