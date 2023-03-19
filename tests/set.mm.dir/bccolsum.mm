include "cn0.mm"
include "wcel.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cbc.mm"
include "csu.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "wi.mm"
include "oveq2.mm"
include "sumeq1d.mm"
include "oveq1.mm"
include "0p1e1.mm"
include "syl6eq.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "weq.mm"
include "cz.mm"
include "cc.mm"
include "0z.mm"
include "0nn0.mm"
include "nn0z.mm"
include "bccl.mm"
include "sylancr.mm"
include "nn0cnd.mm"
include "fsum1.mm"
include "cn.mm"
include "wo.mm"
include "elnn0.mm"
include "cfa.mm"
include "cfv.mm"
include "cmin.mm"
include "cmul.mm"
include "cdiv.mm"
include "cif.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wn.mm"
include "1red.mm"
include "nnrp.mm"
include "ltaddrp2d.mm"
include "peano2nn.mm"
include "nnred.mm"
include "ltnled.mm"
include "mpbid.mm"
include "elfzle2.mm"
include "nsyl.mm"
include "iffalsed.mm"
include "1nn0.mm"
include "nnzd.mm"
include "bcval.mm"
include "bc0k.mm"
include "3eqtr4rd.mm"
include "bcnn.mm"
include "ax-mp.mm"
include "eqtr4i.mm"
include "oveq2d.mm"
include "3eqtr4a.mm"
include "jaoi.mm"
include "sylbi.mm"
include "eqtrd.mm"
include "wa.mm"
include "cuz.mm"
include "elnn0uz.mm"
include "biimpi.mm"
include "adantr.mm"
include "elfznn0.mm"
include "adantl.mm"
include "simplr.mm"
include "nn0zd.mm"
include "syl2anc.mm"
include "fsump1.mm"
include "id.mm"
include "nn0cn.mm"
include "1cnd.mm"
include "pncand.mm"
include "eqcomd.mm"
include "oveqan12rd.mm"
include "peano2nn0.mm"
include "bcpasc.mm"
include "syl2an.mm"
include "3eqtrd.mm"
include "exp31.mm"
include "a2d.mm"
include "nn0ind.mm"
include "imp.mm"

theorem bccolsum
  let cC: class C
  let vk: setvar k
  let cN: class N
  let vn: setvar n
  let vm: setvar m

  disjoint N k
  disjoint C k
  disjoint N n
  disjoint N m
  disjoint m n
  disjoint k n
  disjoint k m
  disjoint C n
  disjoint C m
  assert |- ( ( N e. NN0 /\ C e. NN0 ) -> sum_ k e. ( 0 ... N ) ( k _C C ) = ( ( N + 1 ) _C ( C + 1 ) ) )

  proof
    cN
    cn0
    wcel
    cC
    cn0
    wcel
    #
    cc0
    cN
    cfz
    co
    #
    vk
    cv
    #
    cC
    cbc
    co
    #
    vk
    csu
    #
    cN
    c1
    caddc
    co
    #
    cC
    c1
    caddc
    co
    #
    cbc
    co
    #
    wceq
    #
    @0
    cc0
    vm
    cv
    #
    cfz
    co
    #
    @3
    vk
    csu
    #
    @9
    c1
    caddc
    co
    #
    @6
    cbc
    co
    #
    wceq
    #
    wi
    @0
    cc0
    cc0
    cfz
    co
    #
    @3
    vk
    csu
    #
    c1
    @6
    cbc
    co
    #
    wceq
    #
    wi
    @0
    cc0
    vn
    cv
    #
    cfz
    co
    #
    @3
    vk
    csu
    #
    @19
    c1
    caddc
    co
    #
    @6
    cbc
    co
    #
    wceq
    #
    wi
    @0
    cc0
    @22
    cfz
    co
    #
    @3
    vk
    csu
    #
    @22
    c1
    caddc
    co
    #
    @6
    cbc
    co
    #
    wceq
    #
    wi
    @0
    @8
    wi
    vm
    vn
    cN
    @9
    cc0
    wceq
    #
    @14
    @18
    @0
    @30
    @11
    @16
    @13
    @17
    @30
    @10
    @15
    @3
    vk
    @9
    cc0
    cc0
    cfz
    oveq2
    sumeq1d
    @30
    @12
    c1
    @6
    cbc
    @30
    @12
    cc0
    c1
    caddc
    co
    #
    c1
    @9
    cc0
    c1
    caddc
    oveq1
    0p1e1
    syl6eq
    oveq1d
    eqeq12d
    imbi2d
    vm
    vn
    weq
    #
    @14
    @24
    @0
    @32
    @11
    @21
    @13
    @23
    @32
    @10
    @20
    @3
    vk
    @9
    @19
    cc0
    cfz
    oveq2
    sumeq1d
    @32
    @12
    @22
    @6
    cbc
    @9
    @19
    c1
    caddc
    oveq1
    oveq1d
    eqeq12d
    imbi2d
    @9
    @22
    wceq
    #
    @14
    @29
    @0
    @33
    @11
    @26
    @13
    @28
    @33
    @10
    @25
    @3
    vk
    @9
    @22
    cc0
    cfz
    oveq2
    sumeq1d
    @33
    @12
    @27
    @6
    cbc
    @9
    @22
    c1
    caddc
    oveq1
    oveq1d
    eqeq12d
    imbi2d
    @9
    cN
    wceq
    #
    @14
    @8
    @0
    @34
    @11
    @4
    @13
    @7
    @34
    @10
    @1
    @3
    vk
    @9
    cN
    cc0
    cfz
    oveq2
    sumeq1d
    @34
    @12
    @5
    @6
    cbc
    @9
    cN
    c1
    caddc
    oveq1
    oveq1d
    eqeq12d
    imbi2d
    @0
    @16
    cc0
    cC
    cbc
    co
    #
    @17
    @0
    cc0
    cz
    wcel
    @35
    cc
    wcel
    @16
    @35
    wceq
    0z
    @0
    @35
    @0
    cc0
    cn0
    wcel
    #
    cC
    cz
    wcel
    #
    @35
    cn0
    wcel
    0nn0
    cC
    nn0z
    cC
    cc0
    bccl
    sylancr
    nn0cnd
    @3
    @35
    vk
    cc0
    @2
    cc0
    cC
    cbc
    oveq1
    fsum1
    sylancr
    @0
    cC
    cn
    wcel
    #
    cC
    cc0
    wceq
    #
    wo
    @35
    @17
    wceq
    #
    cC
    elnn0
    @38
    @40
    @39
    @38
    @6
    cc0
    c1
    cfz
    co
    wcel
    #
    c1
    cfa
    cfv
    c1
    @6
    cmin
    co
    cfa
    cfv
    @6
    cfa
    cfv
    cmul
    co
    cdiv
    co
    #
    cc0
    cif
    #
    cc0
    @17
    @35
    @38
    @41
    @42
    cc0
    @38
    @6
    c1
    cle
    wbr
    #
    @41
    @38
    c1
    @6
    clt
    wbr
    @44
    wn
    @38
    c1
    cC
    @38
    1red
    #
    cC
    nnrp
    ltaddrp2d
    @38
    c1
    @6
    @45
    @38
    @6
    cC
    peano2nn
    #
    nnred
    ltnled
    mpbid
    @6
    cc0
    c1
    elfzle2
    nsyl
    iffalsed
    @38
    c1
    cn0
    wcel
    #
    @6
    cz
    wcel
    #
    @17
    @43
    wceq
    1nn0
    @38
    @6
    @46
    nnzd
    @6
    c1
    bcval
    sylancr
    cC
    bc0k
    3eqtr4rd
    @39
    cc0
    cc0
    cbc
    co
    #
    c1
    c1
    cbc
    co
    #
    @35
    @17
    @49
    c1
    @50
    @36
    @49
    c1
    wceq
    0nn0
    cc0
    bcnn
    ax-mp
    @47
    @50
    c1
    wceq
    1nn0
    c1
    bcnn
    ax-mp
    eqtr4i
    cC
    cc0
    cc0
    cbc
    oveq2
    @39
    @6
    c1
    c1
    cbc
    @39
    @6
    @31
    c1
    cC
    cc0
    c1
    caddc
    oveq1
    0p1e1
    syl6eq
    oveq2d
    3eqtr4a
    jaoi
    sylbi
    eqtrd
    @19
    cn0
    wcel
    #
    @0
    @24
    @29
    @51
    @0
    @24
    @29
    @51
    @0
    wa
    #
    @24
    wa
    @26
    @21
    @22
    cC
    cbc
    co
    #
    caddc
    co
    #
    @23
    @22
    @6
    c1
    cmin
    co
    #
    cbc
    co
    #
    caddc
    co
    #
    @28
    @52
    @26
    @54
    wceq
    @24
    @52
    @3
    @53
    vk
    cc0
    @19
    @51
    @19
    cc0
    cuz
    cfv
    wcel
    #
    @0
    @51
    @58
    @19
    elnn0uz
    biimpi
    adantr
    @52
    @2
    @25
    wcel
    #
    wa
    #
    @3
    @60
    @2
    cn0
    wcel
    #
    @37
    @3
    cn0
    wcel
    @59
    @61
    @52
    @2
    @22
    elfznn0
    adantl
    @60
    cC
    @51
    @0
    @59
    simplr
    nn0zd
    cC
    @2
    bccl
    syl2anc
    nn0cnd
    @2
    @22
    cC
    cbc
    oveq1
    fsump1
    adantr
    @24
    @52
    @21
    @23
    @53
    @56
    caddc
    @24
    id
    @52
    @56
    @53
    @52
    @55
    cC
    @22
    cbc
    @52
    cC
    c1
    @0
    cC
    cc
    wcel
    @51
    cC
    nn0cn
    adantl
    @52
    1cnd
    pncand
    oveq2d
    eqcomd
    oveqan12rd
    @52
    @57
    @28
    wceq
    #
    @24
    @51
    @22
    cn0
    wcel
    @48
    @62
    @0
    @19
    peano2nn0
    @0
    @6
    cC
    peano2nn0
    nn0zd
    @6
    @22
    bcpasc
    syl2an
    adantr
    3eqtrd
    exp31
    a2d
    nn0ind
    imp
end
