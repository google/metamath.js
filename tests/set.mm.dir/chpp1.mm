include "cn0.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "cv.mm"
include "cvma.mm"
include "cfv.mm"
include "csu.mm"
include "cmin.mm"
include "cchp.mm"
include "cn.mm"
include "cuz.mm"
include "nn0p1nn.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "wa.mm"
include "cr.mm"
include "elfznn.mm"
include "adantl.mm"
include "vmacl.mm"
include "syl.mm"
include "recnd.mm"
include "fveq2.mm"
include "fsumm1.mm"
include "cfl.mm"
include "wceq.mm"
include "nn0re.mm"
include "peano2re.mm"
include "chpval.mm"
include "3syl.mm"
include "cz.mm"
include "nn0z.mm"
include "peano2zd.mm"
include "flid.mm"
include "oveq2d.mm"
include "sumeq1d.mm"
include "eqtrd.mm"
include "cc.mm"
include "nn0cn.mm"
include "ax-1cn.mm"
include "pncan.mm"
include "sylancl.mm"
include "eqtr4d.mm"
include "oveq1d.mm"
include "3eqtr4d.mm"

theorem chpp1
  let cA: class A
  let vk: setvar k
  let vn: setvar n
  let vp: setvar p
  let vq: setvar q
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cK: class K
  let cM: class M
  let cN: class N
  let cS: class S
  let cB: class B
  let cP: class P


  assert |- ( A e. NN0 -> ( psi ` ( A + 1 ) ) = ( ( psi ` A ) + ( Lam ` ( A + 1 ) ) ) )

  proof
    cA
    cn0
    wcel
    #
    c1
    cA
    c1
    caddc
    co
    #
    cfz
    co
    #
    vn
    cv
    #
    cvma
    cfv
    #
    vn
    csu
    #
    c1
    @1
    c1
    cmin
    co
    #
    cfz
    co
    #
    @4
    vn
    csu
    #
    @1
    cvma
    cfv
    #
    caddc
    co
    @1
    cchp
    cfv
    #
    cA
    cchp
    cfv
    #
    @9
    caddc
    co
    @0
    @4
    @9
    vn
    c1
    @1
    @0
    @1
    cn
    c1
    cuz
    cfv
    cA
    nn0p1nn
    nnuz
    syl6eleq
    @0
    @3
    @2
    wcel
    #
    wa
    #
    @4
    @13
    @3
    cn
    wcel
    #
    @4
    cr
    wcel
    @12
    @14
    @0
    @3
    @1
    elfznn
    adantl
    @3
    vmacl
    syl
    recnd
    @3
    @1
    cvma
    fveq2
    fsumm1
    @0
    @10
    c1
    @1
    cfl
    cfv
    #
    cfz
    co
    #
    @4
    vn
    csu
    #
    @5
    @0
    cA
    cr
    wcel
    #
    @1
    cr
    wcel
    @10
    @17
    wceq
    cA
    nn0re
    #
    cA
    peano2re
    @1
    vn
    chpval
    3syl
    @0
    @16
    @2
    @4
    vn
    @0
    @15
    @1
    c1
    cfz
    @0
    @1
    cz
    wcel
    @15
    @1
    wceq
    @0
    cA
    cA
    nn0z
    #
    peano2zd
    @1
    flid
    syl
    oveq2d
    sumeq1d
    eqtrd
    @0
    @11
    @8
    @9
    caddc
    @0
    @11
    c1
    cA
    cfl
    cfv
    #
    cfz
    co
    #
    @4
    vn
    csu
    #
    @8
    @0
    @18
    @11
    @23
    wceq
    @19
    cA
    vn
    chpval
    syl
    @0
    @22
    @7
    @4
    vn
    @0
    @21
    @6
    c1
    cfz
    @0
    @21
    cA
    @6
    @0
    cA
    cz
    wcel
    @21
    cA
    wceq
    @20
    cA
    flid
    syl
    @0
    cA
    cc
    wcel
    c1
    cc
    wcel
    @6
    cA
    wceq
    cA
    nn0cn
    ax-1cn
    cA
    c1
    pncan
    sylancl
    eqtr4d
    oveq2d
    sumeq1d
    eqtrd
    oveq1d
    3eqtr4d
end
