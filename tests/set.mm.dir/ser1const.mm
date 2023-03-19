include "cn.mm"
include "wcel.mm"
include "cc.mm"
include "caddc.mm"
include "csn.mm"
include "cxp.mm"
include "c1.mm"
include "cseq.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "wi.mm"
include "fveq2.mm"
include "oveq1.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "1z.mm"
include "1nn.mm"
include "fvconst2g.mm"
include "mpan2.mm"
include "mulid2.mm"
include "eqtr4d.mm"
include "seq1i.mm"
include "wa.mm"
include "cuz.mm"
include "seqp1.mm"
include "nnuz.mm"
include "eleq2s.mm"
include "adantl.mm"
include "peano2nn.mm"
include "sylan2.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "nncn.mm"
include "id.mm"
include "ax-1cn.mm"
include "adddir.mm"
include "mp3an2.mm"
include "syl2anr.mm"
include "adantr.mm"
include "syl5ibr.mm"
include "expcom.mm"
include "a2d.mm"
include "nnind.mm"
include "impcom.mm"

theorem ser1const
  let cA: class A
  let cN: class N
  let vj: setvar j
  let vk: setvar k


  assert |- ( ( A e. CC /\ N e. NN ) -> ( seq 1 ( + , ( NN X. { A } ) ) ` N ) = ( N x. A ) )

  proof
    cN
    cn
    wcel
    cA
    cc
    wcel
    #
    cN
    caddc
    cn
    cA
    csn
    cxp
    #
    c1
    cseq
    #
    cfv
    #
    cN
    cA
    cmul
    co
    #
    wceq
    #
    @0
    vj
    cv
    #
    @2
    cfv
    #
    @6
    cA
    cmul
    co
    #
    wceq
    #
    wi
    @0
    c1
    @2
    cfv
    #
    c1
    cA
    cmul
    co
    #
    wceq
    #
    wi
    @0
    vk
    cv
    #
    @2
    cfv
    #
    @13
    cA
    cmul
    co
    #
    wceq
    #
    wi
    @0
    @13
    c1
    caddc
    co
    #
    @2
    cfv
    #
    @17
    cA
    cmul
    co
    #
    wceq
    #
    wi
    @0
    @5
    wi
    vj
    vk
    cN
    @6
    c1
    wceq
    #
    @9
    @12
    @0
    @21
    @7
    @10
    @8
    @11
    @6
    c1
    @2
    fveq2
    @6
    c1
    cA
    cmul
    oveq1
    eqeq12d
    imbi2d
    @6
    @13
    wceq
    #
    @9
    @16
    @0
    @22
    @7
    @14
    @8
    @15
    @6
    @13
    @2
    fveq2
    @6
    @13
    cA
    cmul
    oveq1
    eqeq12d
    imbi2d
    @6
    @17
    wceq
    #
    @9
    @20
    @0
    @23
    @7
    @18
    @8
    @19
    @6
    @17
    @2
    fveq2
    @6
    @17
    cA
    cmul
    oveq1
    eqeq12d
    imbi2d
    @6
    cN
    wceq
    #
    @9
    @5
    @0
    @24
    @7
    @3
    @8
    @4
    @6
    cN
    @2
    fveq2
    @6
    cN
    cA
    cmul
    oveq1
    eqeq12d
    imbi2d
    @0
    @11
    caddc
    @1
    c1
    1z
    @0
    c1
    @1
    cfv
    #
    cA
    @11
    @0
    c1
    cn
    wcel
    @25
    cA
    wceq
    1nn
    cn
    cA
    c1
    cc
    fvconst2g
    mpan2
    cA
    mulid2
    #
    eqtr4d
    seq1i
    @13
    cn
    wcel
    #
    @0
    @16
    @20
    @0
    @27
    @16
    @20
    wi
    @16
    @20
    @0
    @27
    wa
    #
    @14
    cA
    caddc
    co
    #
    @15
    cA
    caddc
    co
    #
    wceq
    @14
    @15
    cA
    caddc
    oveq1
    @28
    @18
    @29
    @19
    @30
    @28
    @18
    @14
    @17
    @1
    cfv
    #
    caddc
    co
    #
    @29
    @27
    @18
    @32
    wceq
    #
    @0
    @33
    @13
    c1
    cuz
    cfv
    cn
    caddc
    @1
    c1
    @13
    seqp1
    nnuz
    eleq2s
    adantl
    @28
    @31
    cA
    @14
    caddc
    @27
    @0
    @17
    cn
    wcel
    @31
    cA
    wceq
    @13
    peano2nn
    cn
    cA
    @17
    cc
    fvconst2g
    sylan2
    oveq2d
    eqtrd
    @28
    @19
    @15
    @11
    caddc
    co
    #
    @30
    @27
    @13
    cc
    wcel
    #
    @0
    @19
    @34
    wceq
    #
    @0
    @13
    nncn
    @0
    id
    @35
    c1
    cc
    wcel
    @0
    @36
    ax-1cn
    @13
    c1
    cA
    adddir
    mp3an2
    syl2anr
    @28
    @11
    cA
    @15
    caddc
    @0
    @11
    cA
    wceq
    @27
    @26
    adantr
    oveq2d
    eqtrd
    eqeq12d
    syl5ibr
    expcom
    a2d
    nnind
    impcom
end
