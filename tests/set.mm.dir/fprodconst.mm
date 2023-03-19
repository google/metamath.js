include "cfn.mm"
include "wcel.mm"
include "cc.mm"
include "wa.mm"
include "c0.mm"
include "wceq.mm"
include "cprod.mm"
include "chash.mm"
include "cfv.mm"
include "cexp.mm"
include "co.mm"
include "cn.mm"
include "c1.mm"
include "cfz.mm"
include "cv.mm"
include "wf1o.mm"
include "wex.mm"
include "wi.mm"
include "cc0.mm"
include "exp0.mm"
include "eqcomd.mm"
include "prodeq1.mm"
include "prod0.mm"
include "syl6eq.mm"
include "fveq2.mm"
include "hash0.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "syl5ibrcom.mm"
include "adantl.mm"
include "cmul.mm"
include "csn.mm"
include "cxp.mm"
include "cseq.mm"
include "eqidd.mm"
include "simprl.mm"
include "simprr.mm"
include "simpllr.mm"
include "elfznn.mm"
include "fvconst2g.mm"
include "syl2anc.mm"
include "fprod.mm"
include "expnnval.mm"
include "ad2ant2lr.mm"
include "eqtr4d.mm"
include "expr.mm"
include "exlimdv.mm"
include "expimpd.mm"
include "wo.mm"
include "fz1f1o.mm"
include "adantr.mm"
include "mpjaod.mm"

theorem fprodconst
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vf: setvar f
  let vn: setvar n

  disjoint A k
  disjoint B k
  disjoint A f
  disjoint A n
  disjoint f k
  disjoint f n
  disjoint k n
  disjoint B f
  disjoint B n
  assert |- ( ( A e. Fin /\ B e. CC ) -> prod_ k e. A B = ( B ^ ( # ` A ) ) )

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
    cprod
    #
    cB
    cA
    chash
    cfv
    #
    cexp
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
    @1
    @3
    @7
    wi
    @0
    @1
    @7
    @3
    c1
    cB
    cc0
    cexp
    co
    #
    wceq
    @1
    @14
    c1
    cB
    exp0
    eqcomd
    @3
    @4
    c1
    @6
    @14
    @3
    @4
    c0
    cB
    vk
    cprod
    c1
    cA
    c0
    cB
    vk
    prodeq1
    cB
    vk
    prod0
    syl6eq
    @3
    @5
    cc0
    cB
    cexp
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
    oveq2d
    eqeq12d
    syl5ibrcom
    adantl
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
    cmul
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
    @20
    @9
    wcel
    #
    wa
    @1
    @20
    cn
    wcel
    #
    @20
    @17
    cfv
    cB
    wceq
    @0
    @1
    @15
    @21
    simpllr
    @21
    @22
    @16
    @20
    @5
    elfznn
    adantl
    cn
    cB
    @20
    cc
    fvconst2g
    syl2anc
    fprod
    @1
    @8
    @6
    @18
    wceq
    @0
    @11
    cB
    @5
    expnnval
    ad2ant2lr
    eqtr4d
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
