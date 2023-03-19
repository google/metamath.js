include "cn0.mm"
include "wcel.mm"
include "cc.mm"
include "wa.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cbc.mm"
include "cbp.mm"
include "cmin.mm"
include "c1.mm"
include "caddc.mm"
include "cdiv.mm"
include "cmul.mm"
include "csu.mm"
include "cexp.mm"
include "cuz.mm"
include "cfv.mm"
include "simpl.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "cz.mm"
include "elfzelz.mm"
include "bccl.mm"
include "syl2an.mm"
include "nn0cnd.mm"
include "elfznn0.mm"
include "simpr.mm"
include "bpolycl.mm"
include "syl2anr.mm"
include "cn.mm"
include "fznn0sub.mm"
include "adantl.mm"
include "nn0p1nn.mm"
include "syl.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "divcld.mm"
include "mulcld.mm"
include "wceq.mm"
include "oveq2.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "oveq12d.mm"
include "fsumm1.mm"
include "bcnn.mm"
include "adantr.mm"
include "nn0cn.mm"
include "subidd.mm"
include "0p1e1.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "div1d.mm"
include "eqtrd.mm"
include "mulid2d.mm"
include "bpolyval.mm"
include "eqcomd.mm"
include "expcl.mm"
include "ancoms.mm"
include "fzfid.mm"
include "fzssp1.mm"
include "ax-1cn.mm"
include "npcan.mm"
include "sylancl.mm"
include "syl5sseq.mm"
include "sselda.mm"
include "syldan.mm"
include "fsumcl.mm"
include "subaddd.mm"
include "mpbid.mm"
include "3eqtrd.mm"

theorem bpolysum
  let vk: setvar k
  let cN: class N
  let cX: class X

  disjoint N k
  disjoint X k
  assert |- ( ( N e. NN0 /\ X e. CC ) -> sum_ k e. ( 0 ... N ) ( ( N _C k ) x. ( ( k BernPoly X ) / ( ( N - k ) + 1 ) ) ) = ( X ^ N ) )

  proof
    cN
    cn0
    wcel
    #
    cX
    cc
    wcel
    #
    wa
    #
    cc0
    cN
    cfz
    co
    #
    cN
    vk
    cv
    #
    cbc
    co
    #
    @4
    cX
    cbp
    co
    #
    cN
    @4
    cmin
    co
    #
    c1
    caddc
    co
    #
    cdiv
    co
    #
    cmul
    co
    #
    vk
    csu
    cc0
    cN
    c1
    cmin
    co
    #
    cfz
    co
    #
    @10
    vk
    csu
    #
    cN
    cN
    cbc
    co
    #
    cN
    cX
    cbp
    co
    #
    cN
    cN
    cmin
    co
    #
    c1
    caddc
    co
    #
    cdiv
    co
    #
    cmul
    co
    #
    caddc
    co
    @13
    @15
    caddc
    co
    #
    cX
    cN
    cexp
    co
    #
    @2
    @10
    @19
    vk
    cc0
    cN
    @2
    cN
    cn0
    cc0
    cuz
    cfv
    @0
    @1
    simpl
    #
    nn0uz
    syl6eleq
    @2
    @4
    @3
    wcel
    #
    wa
    #
    @5
    @9
    @24
    @5
    @2
    @0
    @4
    cz
    wcel
    @5
    cn0
    wcel
    @23
    @22
    @4
    cc0
    cN
    elfzelz
    @4
    cN
    bccl
    syl2an
    nn0cnd
    @24
    @6
    @8
    @23
    @4
    cn0
    wcel
    @1
    @6
    cc
    wcel
    @2
    @4
    cN
    elfznn0
    @0
    @1
    simpr
    @4
    cX
    bpolycl
    syl2anr
    @24
    @8
    @24
    @7
    cn0
    wcel
    #
    @8
    cn
    wcel
    @23
    @25
    @2
    @4
    cc0
    cN
    fznn0sub
    adantl
    @7
    nn0p1nn
    syl
    #
    nncnd
    @24
    @8
    @26
    nnne0d
    divcld
    mulcld
    #
    @4
    cN
    wceq
    #
    @5
    @14
    @9
    @18
    cmul
    @4
    cN
    cN
    cbc
    oveq2
    @28
    @6
    @15
    @8
    @17
    cdiv
    @4
    cN
    cX
    cbp
    oveq1
    @28
    @7
    @16
    c1
    caddc
    @4
    cN
    cN
    cmin
    oveq2
    oveq1d
    oveq12d
    oveq12d
    fsumm1
    @2
    @19
    @15
    @13
    caddc
    @2
    @19
    c1
    @15
    cmul
    co
    @15
    @2
    @14
    c1
    @18
    @15
    cmul
    @0
    @14
    c1
    wceq
    @1
    cN
    bcnn
    adantr
    @2
    @18
    @15
    c1
    cdiv
    co
    @15
    @2
    @17
    c1
    @15
    cdiv
    @2
    @17
    cc0
    c1
    caddc
    co
    c1
    @2
    @16
    cc0
    c1
    caddc
    @2
    cN
    @0
    cN
    cc
    wcel
    #
    @1
    cN
    nn0cn
    adantr
    #
    subidd
    oveq1d
    0p1e1
    syl6eq
    oveq2d
    @2
    @15
    cN
    cX
    bpolycl
    #
    div1d
    eqtrd
    oveq12d
    @2
    @15
    @31
    mulid2d
    eqtrd
    oveq2d
    @2
    @21
    @13
    cmin
    co
    #
    @15
    wceq
    @20
    @21
    wceq
    @2
    @15
    @32
    vk
    cN
    cX
    bpolyval
    eqcomd
    @2
    @21
    @13
    @15
    @1
    @0
    @21
    cc
    wcel
    cX
    cN
    expcl
    ancoms
    @2
    @12
    @10
    vk
    @2
    cc0
    @11
    fzfid
    @2
    @4
    @12
    wcel
    @23
    @10
    cc
    wcel
    @2
    @12
    @3
    @4
    @2
    cc0
    @11
    c1
    caddc
    co
    #
    cfz
    co
    @12
    @3
    cc0
    @11
    fzssp1
    @2
    @33
    cN
    cc0
    cfz
    @2
    @29
    c1
    cc
    wcel
    @33
    cN
    wceq
    @30
    ax-1cn
    cN
    c1
    npcan
    sylancl
    oveq2d
    syl5sseq
    sselda
    @27
    syldan
    fsumcl
    @31
    subaddd
    mpbid
    3eqtrd
end
