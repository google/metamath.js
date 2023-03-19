include "cn0.mm"
include "wcel.mm"
include "c2.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cmul.mm"
include "cbc.mm"
include "cmin.mm"
include "cdiv.mm"
include "2t1e2.mm"
include "df-2.mm"
include "eqtri.mm"
include "oveq2i.mm"
include "cc.mm"
include "wceq.mm"
include "nn0cn.mm"
include "2cn.mm"
include "ax-1cn.mm"
include "adddi.mm"
include "mp3an13.mm"
include "syl.mm"
include "2nn0.mm"
include "nn0mulcl.mm"
include "mpan.mm"
include "nn0cnd.mm"
include "addass.mm"
include "mp3an23.mm"
include "3eqtr4a.mm"
include "oveq1d.mm"
include "cz.mm"
include "peano2nn0.mm"
include "nn0p1nn.mm"
include "nnzd.mm"
include "bcpasc.mm"
include "syl2anc.mm"
include "eqtr4d.mm"
include "nn0z.mm"
include "bccl.mm"
include "2cnd.mm"
include "nn0red.mm"
include "nndivred.mm"
include "recnd.mm"
include "mul12d.mm"
include "1cnd.mm"
include "addsubd.mm"
include "2timesd.mm"
include "pncand.mm"
include "eqtrd.mm"
include "eqtr2d.mm"
include "oveq2d.mm"
include "cc0.mm"
include "cfz.mm"
include "fzctr.mm"
include "bcp1n.mm"
include "bccmpl.mm"
include "addassd.mm"
include "nncnd.mm"
include "pncan.mm"
include "sylancl.mm"
include "oveq12d.mm"

theorem bcp1ctr
  let cN: class N


  assert |- ( N e. NN0 -> ( ( 2 x. ( N + 1 ) ) _C ( N + 1 ) ) = ( ( ( 2 x. N ) _C N ) x. ( 2 x. ( ( ( 2 x. N ) + 1 ) / ( N + 1 ) ) ) ) )

  proof
    cN
    cn0
    wcel
    #
    c2
    cN
    c1
    caddc
    co
    #
    cmul
    co
    #
    @1
    cbc
    co
    #
    c2
    cN
    cmul
    co
    #
    c1
    caddc
    co
    #
    @1
    cbc
    co
    #
    @5
    @1
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
    @4
    cN
    cbc
    co
    #
    c2
    @5
    @1
    cdiv
    co
    #
    cmul
    co
    cmul
    co
    #
    @0
    @3
    @5
    c1
    caddc
    co
    #
    @1
    cbc
    co
    #
    @9
    @0
    @2
    @13
    @1
    cbc
    @0
    @4
    c2
    c1
    cmul
    co
    #
    caddc
    co
    #
    @4
    c1
    c1
    caddc
    co
    #
    caddc
    co
    #
    @2
    @13
    @15
    @17
    @4
    caddc
    @15
    c2
    @17
    2t1e2
    df-2
    eqtri
    oveq2i
    @0
    cN
    cc
    wcel
    #
    @2
    @16
    wceq
    #
    cN
    nn0cn
    #
    c2
    cc
    wcel
    @19
    c1
    cc
    wcel
    #
    @20
    2cn
    ax-1cn
    c2
    cN
    c1
    adddi
    mp3an13
    syl
    @0
    @4
    cc
    wcel
    #
    @13
    @18
    wceq
    #
    @0
    @4
    c2
    cn0
    wcel
    @0
    @4
    cn0
    wcel
    #
    2nn0
    c2
    cN
    nn0mulcl
    mpan
    #
    nn0cnd
    #
    @23
    @22
    @22
    @24
    ax-1cn
    ax-1cn
    @4
    c1
    c1
    addass
    mp3an23
    syl
    3eqtr4a
    oveq1d
    @0
    @5
    cn0
    wcel
    #
    @1
    cz
    wcel
    #
    @9
    @14
    wceq
    @0
    @25
    @28
    @26
    @4
    peano2nn0
    syl
    #
    @0
    @1
    cN
    nn0p1nn
    #
    nnzd
    #
    @1
    @5
    bcpasc
    syl2anc
    eqtr4d
    @0
    @12
    c2
    @5
    cN
    cbc
    co
    #
    cmul
    co
    #
    @9
    @0
    @12
    c2
    @10
    @11
    cmul
    co
    #
    cmul
    co
    @34
    @0
    @10
    c2
    @11
    @0
    @10
    @0
    @25
    cN
    cz
    wcel
    #
    @10
    cn0
    wcel
    @26
    cN
    nn0z
    #
    cN
    @4
    bccl
    syl2anc
    nn0cnd
    @0
    2cnd
    @0
    @11
    @0
    @5
    @1
    @0
    @5
    @30
    nn0red
    @31
    nndivred
    recnd
    mul12d
    @0
    @35
    @33
    c2
    cmul
    @0
    @35
    @10
    @5
    @5
    cN
    cmin
    co
    #
    cdiv
    co
    #
    cmul
    co
    #
    @33
    @0
    @11
    @39
    @10
    cmul
    @0
    @1
    @38
    @5
    cdiv
    @0
    @38
    @4
    cN
    cmin
    co
    #
    c1
    caddc
    co
    @1
    @0
    @4
    c1
    cN
    @27
    @0
    1cnd
    #
    @21
    addsubd
    @0
    @41
    cN
    c1
    caddc
    @0
    @41
    cN
    cN
    caddc
    co
    #
    cN
    cmin
    co
    cN
    @0
    @4
    @43
    cN
    cmin
    @0
    cN
    @21
    2timesd
    #
    oveq1d
    @0
    cN
    cN
    @21
    @21
    pncand
    eqtrd
    oveq1d
    eqtr2d
    oveq2d
    oveq2d
    @0
    cN
    cc0
    @4
    cfz
    co
    wcel
    @33
    @40
    wceq
    cN
    fzctr
    cN
    @4
    bcp1n
    syl
    eqtr4d
    oveq2d
    eqtrd
    @0
    @9
    @33
    @33
    caddc
    co
    @34
    @0
    @6
    @33
    @8
    @33
    caddc
    @0
    @6
    @5
    @5
    @1
    cmin
    co
    #
    cbc
    co
    #
    @33
    @0
    @28
    @29
    @6
    @46
    wceq
    @30
    @32
    @1
    @5
    bccmpl
    syl2anc
    @0
    @45
    cN
    @5
    cbc
    @0
    @45
    cN
    @1
    caddc
    co
    #
    @1
    cmin
    co
    cN
    @0
    @5
    @47
    @1
    cmin
    @0
    @5
    @43
    c1
    caddc
    co
    @47
    @0
    @4
    @43
    c1
    caddc
    @44
    oveq1d
    @0
    cN
    cN
    c1
    @21
    @21
    @42
    addassd
    eqtrd
    oveq1d
    @0
    cN
    @1
    @21
    @0
    @1
    @31
    nncnd
    pncand
    eqtrd
    oveq2d
    eqtrd
    @0
    @7
    cN
    @5
    cbc
    @0
    @19
    @22
    @7
    cN
    wceq
    @21
    ax-1cn
    cN
    c1
    pncan
    sylancl
    oveq2d
    oveq12d
    @0
    @33
    @0
    @33
    @0
    @28
    @36
    @33
    cn0
    wcel
    @30
    @37
    cN
    @5
    bccl
    syl2anc
    nn0cnd
    2timesd
    eqtr4d
    eqtr4d
    eqtr4d
end
