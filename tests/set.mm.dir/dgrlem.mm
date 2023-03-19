include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "cn0.mm"
include "cc0.mm"
include "csn.mm"
include "cun.mm"
include "wf.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "ccnv.mm"
include "cc.mm"
include "cdif.mm"
include "cima.mm"
include "wral.mm"
include "cz.mm"
include "wrex.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cuz.mm"
include "wceq.mm"
include "cfz.mm"
include "cexp.mm"
include "cmul.mm"
include "csu.mm"
include "cmpt.mm"
include "wa.mm"
include "cmap.mm"
include "wss.mm"
include "elply2.mm"
include "simprbi.mm"
include "simplrr.mm"
include "cvv.mm"
include "wb.mm"
include "simpll.mm"
include "plybss.mm"
include "syl.mm"
include "0cnd.mm"
include "snssd.mm"
include "unssd.mm"
include "cnex.mm"
include "ssexg.mm"
include "sylancl.mm"
include "nn0ex.mm"
include "elmapg.mm"
include "mpbid.mm"
include "ccoe.mm"
include "simplrl.mm"
include "fssd.mm"
include "simprl.mm"
include "simprr.mm"
include "coeeq.mm"
include "syl5req.mm"
include "feq1d.mm"
include "ex.mm"
include "rexlimdvva.mm"
include "mpd.mm"
include "nn0ssz.mm"
include "wi.mm"
include "wne.mm"
include "wfn.mm"
include "ffn.mm"
include "elpreima.mm"
include "3syl.mm"
include "biimpa.mm"
include "simprd.mm"
include "eldifsni.mm"
include "simpld.mm"
include "plyco0.mm"
include "syl2anc.mm"
include "r19.21bi.mm"
include "syldan.mm"
include "ralrimiva.mm"
include "cnveqd.mm"
include "imaeq1d.mm"
include "raleqdv.mm"
include "expr.mm"
include "rexlimdv.mm"
include "reximdva.mm"
include "ssrexv.mm"
include "mpsyl.mm"
include "jca.mm"

theorem dgrlem
  let vx: setvar x
  let cA: class A
  let cS: class S
  let vn: setvar n
  let cF: class F
  let va: setvar a
  let vf: setvar f
  let vk: setvar k
  let vz: setvar z
  assume dgrval.1: |- A = ( coeff ` F )

  disjoint n x
  disjoint A n
  disjoint A x
  disjoint F n
  disjoint F x
  disjoint S n
  disjoint S x
  disjoint a f
  disjoint a n
  disjoint a x
  disjoint A a
  disjoint f n
  disjoint f x
  disjoint A f
  disjoint F a
  disjoint F f
  disjoint a k
  disjoint a z
  disjoint S a
  disjoint k n
  disjoint k x
  disjoint k z
  disjoint S k
  disjoint n z
  disjoint x z
  disjoint S z
  assert |- ( F e. ( Poly ` S ) -> ( A : NN0 --> ( S u. { 0 } ) /\ E. n e. ZZ A. x e. ( `' A " ( CC \ { 0 } ) ) x <_ n ) )

  proof
    cF
    cS
    cply
    cfv
    wcel
    #
    cn0
    cS
    cc0
    csn
    #
    cun
    #
    cA
    wf
    #
    vx
    cv
    #
    vn
    cv
    #
    cle
    wbr
    #
    vx
    cA
    ccnv
    #
    cc
    @1
    cdif
    #
    cima
    #
    wral
    #
    vn
    cz
    wrex
    #
    @0
    va
    cv
    #
    @5
    c1
    caddc
    co
    cuz
    cfv
    cima
    @1
    wceq
    #
    cF
    vz
    cc
    cc0
    @5
    cfz
    co
    vk
    cv
    #
    @12
    cfv
    vz
    cv
    @14
    cexp
    co
    cmul
    co
    vk
    csu
    cmpt
    wceq
    #
    wa
    #
    va
    @2
    cn0
    cmap
    co
    #
    wrex
    #
    vn
    cn0
    wrex
    #
    @3
    @0
    cS
    cc
    wss
    #
    @19
    vz
    cS
    vk
    vn
    cF
    va
    elply2
    simprbi
    #
    @0
    @16
    @3
    vn
    va
    cn0
    @17
    @0
    @5
    cn0
    wcel
    #
    @12
    @17
    wcel
    #
    wa
    #
    wa
    #
    @16
    @3
    @25
    @16
    wa
    #
    cn0
    @2
    @12
    wf
    #
    @3
    @26
    @23
    @27
    @0
    @22
    @23
    @16
    simplrr
    @26
    @2
    cvv
    wcel
    #
    cn0
    cvv
    wcel
    @23
    @27
    wb
    @26
    @2
    cc
    wss
    cc
    cvv
    wcel
    @28
    @26
    cS
    @1
    cc
    @26
    @0
    @20
    @0
    @24
    @16
    simpll
    #
    cS
    cF
    plybss
    syl
    @26
    cc0
    cc
    @26
    0cnd
    snssd
    unssd
    #
    cnex
    @2
    cc
    cvv
    ssexg
    sylancl
    nn0ex
    @2
    cn0
    @12
    cvv
    cvv
    elmapg
    sylancl
    mpbid
    #
    @26
    cn0
    @2
    @12
    cA
    @26
    cA
    cF
    ccoe
    cfv
    @12
    dgrval.1
    @26
    vz
    @12
    cS
    vk
    cF
    @5
    @29
    @0
    @22
    @23
    @16
    simplrl
    #
    @26
    cn0
    @2
    cc
    @12
    @31
    @30
    fssd
    #
    @25
    @13
    @15
    simprl
    #
    @25
    @13
    @15
    simprr
    coeeq
    syl5req
    #
    feq1d
    mpbid
    ex
    rexlimdvva
    mpd
    cn0
    cz
    wss
    @0
    @10
    vn
    cn0
    wrex
    #
    @11
    nn0ssz
    @0
    @19
    @36
    @21
    @0
    @18
    @10
    vn
    cn0
    @0
    @22
    wa
    @16
    @10
    va
    @17
    @0
    @22
    @23
    @16
    @10
    wi
    @25
    @16
    @10
    @26
    @6
    vx
    @12
    ccnv
    #
    @8
    cima
    #
    wral
    @10
    @26
    @6
    vx
    @38
    @26
    @4
    @38
    wcel
    #
    wa
    #
    @4
    @12
    cfv
    #
    cc0
    wne
    #
    @6
    @40
    @41
    @8
    wcel
    #
    @42
    @40
    @4
    cn0
    wcel
    #
    @43
    @26
    @39
    @44
    @43
    wa
    #
    @26
    cn0
    cc
    @12
    wf
    #
    @12
    cn0
    wfn
    @39
    @45
    wb
    @33
    cn0
    cc
    @12
    ffn
    cn0
    @4
    @8
    @12
    elpreima
    3syl
    biimpa
    #
    simprd
    @41
    cc
    cc0
    eldifsni
    syl
    @26
    @39
    @44
    @42
    @6
    wi
    #
    @40
    @44
    @43
    @47
    simpld
    @26
    @48
    vx
    cn0
    @26
    @13
    @48
    vx
    cn0
    wral
    #
    @34
    @26
    @22
    @46
    @13
    @49
    wb
    @32
    @33
    @12
    vx
    @5
    plyco0
    syl2anc
    mpbid
    r19.21bi
    syldan
    mpd
    ralrimiva
    @26
    @6
    vx
    @38
    @9
    @26
    @37
    @7
    @8
    @26
    @12
    cA
    @35
    cnveqd
    imaeq1d
    raleqdv
    mpbid
    ex
    expr
    rexlimdv
    reximdva
    mpd
    @10
    vn
    cn0
    cz
    ssrexv
    mpsyl
    jca
end
