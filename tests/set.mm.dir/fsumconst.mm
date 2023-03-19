include "cfn.mm"
include "wcel.mm"
include "cc.mm"
include "wa.mm"
include "c0.mm"
include "wceq.mm"
include "csu.mm"
include "chash.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "cn.mm"
include "c1.mm"
include "cfz.mm"
include "cv.mm"
include "wf1o.mm"
include "wex.mm"
include "cc0.mm"
include "mul02.mm"
include "adantl.mm"
include "eqcomd.mm"
include "sumeq1.mm"
include "sum0.mm"
include "syl6eq.mm"
include "fveq2.mm"
include "hash0.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "syl5ibrcom.mm"
include "caddc.mm"
include "csn.mm"
include "cxp.mm"
include "cseq.mm"
include "eqidd.mm"
include "simprl.mm"
include "simprr.mm"
include "simpllr.mm"
include "simplr.mm"
include "elfznn.mm"
include "fvconst2g.mm"
include "syl2an.mm"
include "fsum.mm"
include "ser1const.mm"
include "ad2ant2lr.mm"
include "eqtrd.mm"
include "expr.mm"
include "exlimdv.mm"
include "expimpd.mm"
include "wo.mm"
include "fz1f1o.mm"
include "adantr.mm"
include "mpjaod.mm"

theorem fsumconst
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vf: setvar f
  let vn: setvar n

  disjoint A k
  disjoint B k
  disjoint f k
  disjoint f n
  disjoint A f
  disjoint k n
  disjoint A n
  disjoint B f
  disjoint B n
  assert |- ( ( A e. Fin /\ B e. CC ) -> sum_ k e. A B = ( ( # ` A ) x. B ) )

  proof
    cA
    cfn
    wcel
    #
    cB
    cc
    wcel
    #
    wa
    #
    cA
    c0
    wceq
    #
    cA
    cB
    vk
    csu
    #
    cA
    chash
    cfv
    #
    cB
    cmul
    co
    #
    wceq
    #
    @5
    cn
    wcel
    #
    c1
    @5
    cfz
    co
    #
    cA
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    #
    wa
    #
    @2
    @7
    @3
    cc0
    cc0
    cB
    cmul
    co
    #
    wceq
    @2
    @14
    cc0
    @1
    @14
    cc0
    wceq
    @0
    cB
    mul02
    adantl
    eqcomd
    @3
    @4
    cc0
    @6
    @14
    @3
    @4
    c0
    cB
    vk
    csu
    cc0
    cA
    c0
    cB
    vk
    sumeq1
    cB
    vk
    sum0
    syl6eq
    @3
    @5
    cc0
    cB
    cmul
    @3
    @5
    c0
    chash
    cfv
    cc0
    cA
    c0
    chash
    fveq2
    hash0
    syl6eq
    oveq1d
    eqeq12d
    syl5ibrcom
    @2
    @8
    @12
    @7
    @2
    @8
    wa
    @11
    @7
    vf
    @2
    @8
    @11
    @7
    @2
    @8
    @11
    wa
    #
    wa
    #
    @4
    @5
    caddc
    cn
    cB
    csn
    cxp
    #
    c1
    cseq
    cfv
    #
    @6
    @16
    cA
    cB
    cB
    vk
    vn
    @10
    @17
    @5
    vk
    cv
    #
    vn
    cv
    #
    @10
    cfv
    wceq
    cB
    eqidd
    @2
    @8
    @11
    simprl
    @2
    @8
    @11
    simprr
    @0
    @1
    @15
    @19
    cA
    wcel
    simpllr
    @16
    @1
    @20
    cn
    wcel
    @20
    @17
    cfv
    cB
    wceq
    @20
    @9
    wcel
    @0
    @1
    @15
    simplr
    @20
    @5
    elfznn
    cn
    cB
    @20
    cc
    fvconst2g
    syl2an
    fsum
    @1
    @8
    @18
    @6
    wceq
    @0
    @11
    cB
    @5
    ser1const
    ad2ant2lr
    eqtrd
    expr
    exlimdv
    expimpd
    @0
    @3
    @13
    wo
    @1
    cA
    vf
    fz1f1o
    adantr
    mpjaod
end
