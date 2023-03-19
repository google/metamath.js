include "cn0.mm"
include "wcel.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cc0.mm"
include "cfz.mm"
include "cv.mm"
include "cbc.mm"
include "c1.mm"
include "cmul.mm"
include "csu.mm"
include "caddc.mm"
include "df-2.mm"
include "oveq1i.mm"
include "cc.mm"
include "wceq.mm"
include "ax-1cn.mm"
include "binom1p.mm"
include "mpan.mm"
include "syl5eq.mm"
include "cz.mm"
include "elfzelz.mm"
include "1exp.mm"
include "syl.mm"
include "oveq2d.mm"
include "bccl2.mm"
include "nncnd.mm"
include "mulid1d.mm"
include "eqtrd.mm"
include "sumeq2i.mm"
include "syl6eq.mm"

theorem binom11
  let vk: setvar k
  let cN: class N
  let vn: setvar n
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint N k
  disjoint k n
  disjoint k x
  disjoint A k
  disjoint n x
  disjoint A n
  disjoint A x
  disjoint B k
  disjoint B n
  disjoint B x
  disjoint N x
  assert |- ( N e. NN0 -> ( 2 ^ N ) = sum_ k e. ( 0 ... N ) ( N _C k ) )

  proof
    cN
    cn0
    wcel
    #
    c2
    cN
    cexp
    co
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
    c1
    @3
    cexp
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    @2
    @4
    vk
    csu
    @0
    @1
    c1
    c1
    caddc
    co
    #
    cN
    cexp
    co
    #
    @7
    c2
    @8
    cN
    cexp
    df-2
    oveq1i
    c1
    cc
    wcel
    @0
    @9
    @7
    wceq
    ax-1cn
    c1
    vk
    cN
    binom1p
    mpan
    syl5eq
    @2
    @6
    @4
    vk
    @3
    @2
    wcel
    #
    @6
    @4
    c1
    cmul
    co
    @4
    @10
    @5
    c1
    @4
    cmul
    @10
    @3
    cz
    wcel
    @5
    c1
    wceq
    @3
    cc0
    cN
    elfzelz
    @3
    1exp
    syl
    oveq2d
    @10
    @4
    @10
    @4
    @3
    cN
    bccl2
    nncnd
    mulid1d
    eqtrd
    sumeq2i
    syl6eq
end
