include "cn0.mm"
include "wcel.mm"
include "c2.mm"
include "cbc.mm"
include "co.mm"
include "cmul.mm"
include "cid.mm"
include "cmin.mm"
include "c1.mm"
include "caddc.mm"
include "cseq.mm"
include "cfv.mm"
include "cfa.mm"
include "cdiv.mm"
include "cn.mm"
include "wceq.mm"
include "2nn.mm"
include "bcval5.mm"
include "mpan2.mm"
include "2m1e1.mm"
include "oveq2i.mm"
include "cc.mm"
include "nn0cn.mm"
include "2cn.mm"
include "ax-1cn.mm"
include "npncan.mm"
include "mp3an23.mm"
include "syl.mm"
include "syl5eqr.mm"
include "seqeq1d.mm"
include "fveq1d.mm"
include "cz.mm"
include "cuz.mm"
include "nn0z.mm"
include "peano2zm.mm"
include "uzid.mm"
include "npcan.mm"
include "sylancl.mm"
include "fveq2d.mm"
include "eleqtrrd.mm"
include "seqm1.mm"
include "syl2anc.mm"
include "seq1.mm"
include "fvi.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "subcl.mm"
include "mulcomd.mm"
include "fac2.mm"
include "a1i.mm"

theorem bcn2
  let cN: class N


  assert |- ( N e. NN0 -> ( N _C 2 ) = ( ( N x. ( N - 1 ) ) / 2 ) )

  proof
    cN
    cn0
    wcel
    #
    cN
    c2
    cbc
    co
    #
    cN
    cmul
    cid
    cN
    c2
    cmin
    co
    #
    c1
    caddc
    co
    #
    cseq
    #
    cfv
    #
    c2
    cfa
    cfv
    #
    cdiv
    co
    #
    cN
    cN
    c1
    cmin
    co
    #
    cmul
    co
    #
    c2
    cdiv
    co
    @0
    c2
    cn
    wcel
    @1
    @7
    wceq
    2nn
    c2
    cN
    bcval5
    mpan2
    @0
    @5
    @9
    @6
    c2
    cdiv
    @0
    @5
    cN
    cmul
    cid
    @8
    cseq
    #
    cfv
    #
    @9
    @0
    cN
    @4
    @10
    @0
    @3
    @8
    cmul
    cid
    @0
    @3
    @2
    c2
    c1
    cmin
    co
    #
    caddc
    co
    #
    @8
    @12
    c1
    @2
    caddc
    2m1e1
    oveq2i
    @0
    cN
    cc
    wcel
    #
    @13
    @8
    wceq
    #
    cN
    nn0cn
    #
    @14
    c2
    cc
    wcel
    c1
    cc
    wcel
    #
    @15
    2cn
    ax-1cn
    cN
    c2
    c1
    npncan
    mp3an23
    syl
    syl5eqr
    seqeq1d
    fveq1d
    @0
    @11
    @8
    cN
    cmul
    co
    #
    @9
    @0
    @11
    @8
    @10
    cfv
    #
    cN
    cid
    cfv
    #
    cmul
    co
    #
    @18
    @0
    @8
    cz
    wcel
    #
    cN
    @8
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    wcel
    @11
    @21
    wceq
    @0
    cN
    cz
    wcel
    #
    @22
    cN
    nn0z
    #
    cN
    peano2zm
    syl
    #
    @0
    cN
    cN
    cuz
    cfv
    #
    @24
    @0
    @25
    cN
    @28
    wcel
    @26
    cN
    uzid
    syl
    @0
    @23
    cN
    cuz
    @0
    @14
    @17
    @23
    cN
    wceq
    @16
    ax-1cn
    cN
    c1
    npcan
    sylancl
    fveq2d
    eleqtrrd
    cmul
    cid
    @8
    cN
    seqm1
    syl2anc
    @0
    @19
    @8
    @20
    cN
    cmul
    @0
    @19
    @8
    cid
    cfv
    #
    @8
    @0
    @22
    @19
    @29
    wceq
    @27
    cmul
    cid
    @8
    seq1
    syl
    @0
    @22
    @29
    @8
    wceq
    @27
    @8
    cz
    fvi
    syl
    eqtrd
    cN
    cn0
    fvi
    oveq12d
    eqtrd
    @0
    @8
    cN
    @0
    @14
    @17
    @8
    cc
    wcel
    @16
    ax-1cn
    cN
    c1
    subcl
    sylancl
    @16
    mulcomd
    eqtrd
    eqtrd
    @6
    c2
    wceq
    @0
    fac2
    a1i
    oveq12d
    eqtrd
end
