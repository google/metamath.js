include "cc0.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "cbc.mm"
include "cdiv.mm"
include "wceq.mm"
include "cmul.mm"
include "caddc.mm"
include "bcp1n.mm"
include "cc.mm"
include "nnz.mm"
include "zcnd.mm"
include "adantl.mm"
include "1cnd.mm"
include "npcand.mm"
include "oveq1d.mm"
include "oveq12d.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "syl5ib.mm"
include "3impia.mm"
include "3anidm13.mm"
include "wne.mm"
include "wb.mm"
include "crp.mm"
include "cn0.mm"
include "cle.mm"
include "wbr.mm"
include "elfznn0.mm"
include "adantr.mm"
include "simpr.mm"
include "nnnn0d.mm"
include "cz.mm"
include "elfzelz.mm"
include "zred.mm"
include "clt.mm"
include "elfzle2.mm"
include "zltlem1.mm"
include "syl2an.mm"
include "mpbird.mm"
include "ltled.mm"
include "elfz2nn0.mm"
include "syl3anbrc.mm"
include "bcrpcl.mm"
include "syl.mm"
include "rpcnd.mm"
include "subcld.mm"
include "cneg.mm"
include "negsubdi2d.mm"
include "resubcld.mm"
include "recnd.mm"
include "addid2d.mm"
include "breqtrrd.mm"
include "0red.mm"
include "ltsubaddd.mm"
include "lt0ne0d.mm"
include "negne0d.mm"
include "eqnetrrd.mm"
include "divcld.mm"
include "rpcnne0d.mm"
include "divmul2.mm"
include "syl3anc.mm"
include "bccl2.mm"
include "nnne0d.mm"
include "recdivd.mm"
include "3eqtr3d.mm"

theorem bcm1n
  let cK: class K
  let cN: class N


  assert |- ( ( K e. ( 0 ... ( N - 1 ) ) /\ N e. NN ) -> ( ( ( N - 1 ) _C K ) / ( N _C K ) ) = ( ( N - K ) / N ) )

  proof
    cK
    cc0
    cN
    c1
    cmin
    co
    #
    cfz
    co
    wcel
    #
    cN
    cn
    wcel
    #
    wa
    #
    c1
    cN
    cK
    cbc
    co
    #
    @0
    cK
    cbc
    co
    #
    cdiv
    co
    #
    cdiv
    co
    c1
    cN
    cN
    cK
    cmin
    co
    #
    cdiv
    co
    #
    cdiv
    co
    @5
    @4
    cdiv
    co
    @7
    cN
    cdiv
    co
    @3
    @6
    @8
    c1
    cdiv
    @3
    @6
    @8
    wceq
    #
    @4
    @5
    @8
    cmul
    co
    #
    wceq
    #
    @1
    @2
    @11
    @1
    @2
    @1
    @11
    @1
    @0
    c1
    caddc
    co
    #
    cK
    cbc
    co
    #
    @5
    @12
    @12
    cK
    cmin
    co
    #
    cdiv
    co
    #
    cmul
    co
    #
    wceq
    @3
    @11
    cK
    @0
    bcp1n
    @3
    @13
    @4
    @16
    @10
    @3
    @12
    cN
    cK
    cbc
    @3
    cN
    c1
    @2
    cN
    cc
    wcel
    @1
    @2
    cN
    cN
    nnz
    #
    zcnd
    adantl
    #
    @3
    1cnd
    npcand
    #
    oveq1d
    @3
    @15
    @8
    @5
    cmul
    @3
    @12
    cN
    @14
    @7
    cdiv
    @19
    @3
    @12
    cN
    cK
    cmin
    @19
    oveq1d
    oveq12d
    oveq2d
    eqeq12d
    syl5ib
    3impia
    3anidm13
    @3
    @4
    cc
    wcel
    @8
    cc
    wcel
    @5
    cc
    wcel
    @5
    cc0
    wne
    #
    wa
    @9
    @11
    wb
    @3
    @4
    @3
    cK
    cc0
    cN
    cfz
    co
    wcel
    #
    @4
    crp
    wcel
    @3
    cK
    cn0
    wcel
    #
    cN
    cn0
    wcel
    cK
    cN
    cle
    wbr
    @21
    @1
    @22
    @2
    cK
    @0
    elfznn0
    adantr
    @3
    cN
    @1
    @2
    simpr
    #
    nnnn0d
    @3
    cK
    cN
    @3
    cK
    @1
    cK
    cz
    wcel
    #
    @2
    cK
    cc0
    @0
    elfzelz
    #
    adantr
    zred
    #
    @3
    cN
    @2
    cN
    cz
    wcel
    #
    @1
    @17
    adantl
    zred
    #
    @3
    cK
    cN
    clt
    wbr
    #
    cK
    @0
    cle
    wbr
    #
    @1
    @30
    @2
    cK
    cc0
    @0
    elfzle2
    adantr
    @1
    @24
    @27
    @29
    @30
    wb
    @2
    @25
    @17
    cK
    cN
    zltlem1
    syl2an
    mpbird
    #
    ltled
    cK
    cN
    elfz2nn0
    syl3anbrc
    #
    cK
    cN
    bcrpcl
    syl
    rpcnd
    #
    @3
    cN
    @7
    @18
    @3
    cN
    cK
    @18
    @1
    cK
    cc
    wcel
    @2
    @1
    cK
    @25
    zcnd
    adantr
    #
    subcld
    #
    @3
    cK
    cN
    cmin
    co
    #
    cneg
    @7
    cc0
    @3
    cK
    cN
    @34
    @18
    negsubdi2d
    @3
    @36
    @3
    @36
    @3
    cK
    cN
    @26
    @28
    resubcld
    recnd
    @3
    @36
    @3
    @36
    cc0
    clt
    wbr
    cK
    cc0
    cN
    caddc
    co
    #
    clt
    wbr
    @3
    cK
    cN
    @37
    clt
    @31
    @3
    cN
    @18
    addid2d
    breqtrrd
    @3
    cK
    cN
    cc0
    @26
    @28
    @3
    0red
    ltsubaddd
    mpbird
    lt0ne0d
    negne0d
    eqnetrrd
    #
    divcld
    @3
    @5
    @1
    @5
    crp
    wcel
    @2
    cK
    @0
    bcrpcl
    adantr
    #
    rpcnne0d
    @4
    @8
    @5
    divmul2
    syl3anc
    mpbird
    oveq2d
    @3
    @4
    @5
    @33
    @3
    @5
    @39
    rpcnd
    @3
    @4
    @3
    @21
    @4
    cn
    wcel
    @32
    cK
    cN
    bccl2
    syl
    nnne0d
    @1
    @20
    @2
    @1
    @5
    cK
    @0
    bccl2
    nnne0d
    adantr
    recdivd
    @3
    cN
    @7
    @18
    @35
    @3
    cN
    @23
    nnne0d
    @38
    recdivd
    3eqtr3d
end
