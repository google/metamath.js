include "cc.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cexp.mm"
include "cmin.mm"
include "cc0.mm"
include "cfz.mm"
include "cv.mm"
include "cbc.mm"
include "cmul.mm"
include "csu.mm"
include "wceq.mm"
include "simpl.mm"
include "ax-1cn.mm"
include "addcom.mm"
include "sylancl.mm"
include "oveq1d.mm"
include "binom1p.mm"
include "cuz.mm"
include "cfv.mm"
include "simpr.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "cn.mm"
include "bccl2.mm"
include "adantl.mm"
include "nncnd.mm"
include "elfznn0.mm"
include "expcl.mm"
include "syl2an.mm"
include "mulcld.mm"
include "oveq2.mm"
include "oveq12d.mm"
include "fsumm1.mm"
include "bcnn.mm"
include "mulid2d.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "3eqtrd.mm"
include "fzfid.mm"
include "fzssp1.mm"
include "nn0cn.mm"
include "npcan.mm"
include "syl5sseq.mm"
include "sselda.mm"
include "syldan.mm"
include "fsumcl.mm"
include "pncand.mm"

theorem binom1dif
  let cA: class A
  let vk: setvar k
  let cN: class N
  let vn: setvar n
  let vx: setvar x
  let cB: class B

  disjoint A k
  disjoint N k
  disjoint k n
  disjoint k x
  disjoint n x
  disjoint A n
  disjoint A x
  disjoint B k
  disjoint B n
  disjoint B x
  disjoint N x
  assert |- ( ( A e. CC /\ N e. NN0 ) -> ( ( ( A + 1 ) ^ N ) - ( A ^ N ) ) = sum_ k e. ( 0 ... ( N - 1 ) ) ( ( N _C k ) x. ( A ^ k ) ) )

  proof
    cA
    cc
    wcel
    #
    cN
    cn0
    wcel
    #
    wa
    #
    cA
    c1
    caddc
    co
    #
    cN
    cexp
    co
    #
    cA
    cN
    cexp
    co
    #
    cmin
    co
    cc0
    cN
    c1
    cmin
    co
    #
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
    cA
    @8
    cexp
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    @5
    caddc
    co
    #
    @5
    cmin
    co
    @12
    @2
    @4
    @13
    @5
    cmin
    @2
    @4
    c1
    cA
    caddc
    co
    #
    cN
    cexp
    co
    cc0
    cN
    cfz
    co
    #
    @11
    vk
    csu
    #
    @13
    @2
    @3
    @14
    cN
    cexp
    @2
    @0
    c1
    cc
    wcel
    #
    @3
    @14
    wceq
    @0
    @1
    simpl
    #
    ax-1cn
    cA
    c1
    addcom
    sylancl
    oveq1d
    cA
    vk
    cN
    binom1p
    @2
    @16
    @12
    cN
    cN
    cbc
    co
    #
    @5
    cmul
    co
    #
    caddc
    co
    @13
    @2
    @11
    @20
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
    simpr
    nn0uz
    syl6eleq
    @2
    @8
    @15
    wcel
    #
    wa
    #
    @9
    @10
    @22
    @9
    @21
    @9
    cn
    wcel
    @2
    @8
    cN
    bccl2
    adantl
    nncnd
    @2
    @0
    @8
    cn0
    wcel
    @10
    cc
    wcel
    @21
    @18
    @8
    cN
    elfznn0
    cA
    @8
    expcl
    syl2an
    mulcld
    #
    @8
    cN
    wceq
    @9
    @19
    @10
    @5
    cmul
    @8
    cN
    cN
    cbc
    oveq2
    @8
    cN
    cA
    cexp
    oveq2
    oveq12d
    fsumm1
    @2
    @20
    @5
    @12
    caddc
    @2
    @20
    c1
    @5
    cmul
    co
    @5
    @2
    @19
    c1
    @5
    cmul
    @1
    @19
    c1
    wceq
    @0
    cN
    bcnn
    adantl
    oveq1d
    @2
    @5
    cA
    cN
    expcl
    #
    mulid2d
    eqtrd
    oveq2d
    eqtrd
    3eqtrd
    oveq1d
    @2
    @12
    @5
    @2
    @7
    @11
    vk
    @2
    cc0
    @6
    fzfid
    @2
    @8
    @7
    wcel
    @21
    @11
    cc
    wcel
    @2
    @7
    @15
    @8
    @2
    cc0
    @6
    c1
    caddc
    co
    #
    cfz
    co
    @7
    @15
    cc0
    @6
    fzssp1
    @2
    @25
    cN
    cc0
    cfz
    @2
    cN
    cc
    wcel
    #
    @17
    @25
    cN
    wceq
    @1
    @26
    @0
    cN
    nn0cn
    adantl
    ax-1cn
    cN
    c1
    npcan
    sylancl
    oveq2d
    syl5sseq
    sselda
    @23
    syldan
    fsumcl
    @24
    pncand
    eqtrd
end
