include "cc.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cexp.mm"
include "cc0.mm"
include "cfz.mm"
include "cv.mm"
include "cbc.mm"
include "cmin.mm"
include "cmul.mm"
include "csu.mm"
include "wceq.mm"
include "ax-1cn.mm"
include "binom.mm"
include "mp3an1.mm"
include "cz.mm"
include "fznn0sub.mm"
include "adantl.mm"
include "nn0zd.mm"
include "1exp.mm"
include "syl.mm"
include "oveq1d.mm"
include "simpl.mm"
include "elfznn0.mm"
include "expcl.mm"
include "syl2an.mm"
include "mulid2d.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "sumeq2dv.mm"

theorem binom1p
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
  assert |- ( ( A e. CC /\ N e. NN0 ) -> ( ( 1 + A ) ^ N ) = sum_ k e. ( 0 ... N ) ( ( N _C k ) x. ( A ^ k ) ) )

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
    c1
    cA
    caddc
    co
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
    cN
    @5
    cmin
    co
    #
    cexp
    co
    #
    cA
    @5
    cexp
    co
    #
    cmul
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    @4
    @6
    @9
    cmul
    co
    #
    vk
    csu
    c1
    cc
    wcel
    @0
    @1
    @3
    @12
    wceq
    ax-1cn
    c1
    cA
    vk
    cN
    binom
    mp3an1
    @2
    @4
    @11
    @13
    vk
    @2
    @5
    @4
    wcel
    #
    wa
    #
    @10
    @9
    @6
    cmul
    @15
    @10
    c1
    @9
    cmul
    co
    @9
    @15
    @8
    c1
    @9
    cmul
    @15
    @7
    cz
    wcel
    @8
    c1
    wceq
    @15
    @7
    @14
    @7
    cn0
    wcel
    @2
    @5
    cc0
    cN
    fznn0sub
    adantl
    nn0zd
    @7
    1exp
    syl
    oveq1d
    @15
    @9
    @2
    @0
    @5
    cn0
    wcel
    @9
    cc
    wcel
    @14
    @0
    @1
    simpl
    @5
    cN
    elfznn0
    cA
    @5
    expcl
    syl2an
    mulid2d
    eqtrd
    oveq2d
    sumeq2dv
    eqtrd
end
