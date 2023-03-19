include "cz.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "cbits.mm"
include "cfv.mm"
include "cin.mm"
include "cv.mm"
include "cmin.mm"
include "crab.mm"
include "wss.mm"
include "wceq.mm"
include "bitsss.mm"
include "sseqin2.mm"
include "mpbi.mm"
include "cuz.mm"
include "cdvds.mm"
include "wbr.mm"
include "simpll.mm"
include "cn.mm"
include "2nn.mm"
include "a1i.mm"
include "simplr.mm"
include "nnexpcld.mm"
include "nnzd.mm"
include "dvdsmul2.mm"
include "syl2anc.mm"
include "wb.mm"
include "zmulcld.mm"
include "bitsuz.mm"
include "mpbid.mm"
include "sseld.mm"
include "uznn0sub.mm"
include "syl6.mm"
include "cdiv.mm"
include "cfl.mm"
include "wn.mm"
include "2cnd.mm"
include "nnne0d.mm"
include "nn0zd.mm"
include "simprl.mm"
include "expsubd.mm"
include "oveq2d.mm"
include "cc.mm"
include "simpl.mm"
include "zcnd.mm"
include "adantr.mm"
include "nncnd.mm"
include "divdiv2d.mm"
include "eqtr2d.mm"
include "fveq2d.mm"
include "breq2d.mm"
include "notbid.mm"
include "adantrr.mm"
include "bitsval2.mm"
include "ad2ant2rl.mm"
include "3bitr4d.mm"
include "expr.mm"
include "pm5.21ndd.mm"
include "rabbi2dva.mm"
include "syl5reqr.mm"

theorem bitsshft
  let cA: class A
  let vn: setvar n
  let cN: class N

  disjoint A n
  disjoint N n
  assert |- ( ( A e. ZZ /\ N e. NN0 ) -> { n e. NN0 | ( n - N ) e. ( bits ` A ) } = ( bits ` ( A x. ( 2 ^ N ) ) ) )

  proof
    cA
    cz
    wcel
    #
    cN
    cn0
    wcel
    #
    wa
    #
    cA
    c2
    cN
    cexp
    co
    #
    cmul
    co
    #
    cbits
    cfv
    #
    cn0
    @5
    cin
    #
    vn
    cv
    #
    cN
    cmin
    co
    #
    cA
    cbits
    cfv
    #
    wcel
    #
    vn
    cn0
    crab
    @5
    cn0
    wss
    @6
    @5
    wceq
    @4
    bitsss
    @5
    cn0
    sseqin2
    mpbi
    @2
    @10
    vn
    cn0
    @5
    @2
    @7
    cn0
    wcel
    #
    wa
    #
    @8
    cn0
    wcel
    #
    @7
    @5
    wcel
    #
    @10
    @12
    @14
    @7
    cN
    cuz
    cfv
    #
    wcel
    @13
    @12
    @5
    @15
    @7
    @12
    @3
    @4
    cdvds
    wbr
    #
    @5
    @15
    wss
    #
    @12
    @0
    @3
    cz
    wcel
    @16
    @0
    @1
    @11
    simpll
    #
    @12
    @3
    @12
    c2
    cN
    c2
    cn
    wcel
    #
    @12
    2nn
    a1i
    @0
    @1
    @11
    simplr
    #
    nnexpcld
    nnzd
    #
    cA
    @3
    dvdsmul2
    syl2anc
    @12
    @4
    cz
    wcel
    #
    @1
    @16
    @17
    wb
    @12
    cA
    @3
    @18
    @21
    zmulcld
    #
    @20
    @4
    cN
    bitsuz
    syl2anc
    mpbid
    sseld
    cN
    @7
    uznn0sub
    syl6
    @12
    @9
    cn0
    @8
    @9
    cn0
    wss
    @12
    cA
    bitsss
    a1i
    sseld
    @2
    @11
    @13
    @14
    @10
    wb
    @2
    @11
    @13
    wa
    #
    wa
    #
    c2
    @4
    c2
    @7
    cexp
    co
    #
    cdiv
    co
    #
    cfl
    cfv
    #
    cdvds
    wbr
    #
    wn
    #
    c2
    cA
    c2
    @8
    cexp
    co
    #
    cdiv
    co
    #
    cfl
    cfv
    #
    cdvds
    wbr
    #
    wn
    #
    @14
    @10
    @25
    @29
    @34
    @25
    @28
    @33
    c2
    cdvds
    @25
    @27
    @32
    cfl
    @25
    @32
    cA
    @26
    @3
    cdiv
    co
    #
    cdiv
    co
    @27
    @25
    @31
    @36
    cA
    cdiv
    @25
    c2
    @7
    cN
    @25
    2cnd
    @25
    c2
    @19
    @25
    2nn
    a1i
    #
    nnne0d
    @25
    cN
    @0
    @1
    @24
    simplr
    #
    nn0zd
    @25
    @7
    @2
    @11
    @13
    simprl
    #
    nn0zd
    expsubd
    oveq2d
    @25
    cA
    @26
    @3
    @2
    cA
    cc
    wcel
    @24
    @2
    cA
    @0
    @1
    simpl
    zcnd
    adantr
    @25
    @26
    @25
    c2
    @7
    @37
    @39
    nnexpcld
    #
    nncnd
    @25
    @3
    @25
    c2
    cN
    @37
    @38
    nnexpcld
    #
    nncnd
    @25
    @26
    @40
    nnne0d
    @25
    @3
    @41
    nnne0d
    divdiv2d
    eqtr2d
    fveq2d
    breq2d
    notbid
    @25
    @22
    @11
    @14
    @30
    wb
    @2
    @11
    @22
    @13
    @23
    adantrr
    @39
    @7
    @4
    bitsval2
    syl2anc
    @0
    @13
    @10
    @35
    wb
    @1
    @11
    @8
    cA
    bitsval2
    ad2ant2rl
    3bitr4d
    expr
    pm5.21ndd
    rabbi2dva
    syl5reqr
end
