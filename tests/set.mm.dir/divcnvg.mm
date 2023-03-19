include "cc.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "cuz.mm"
include "cfv.mm"
include "cv.mm"
include "cdiv.mm"
include "co.mm"
include "cmpt.mm"
include "cc0.mm"
include "cli.mm"
include "wceq.mm"
include "eluznn.mm"
include "cvv.mm"
include "eqidd.mm"
include "oveq2.mm"
include "adantl.mm"
include "id.mm"
include "ovexd.mm"
include "fvmptd.mm"
include "eqcomd.mm"
include "syl.mm"
include "adantll.mm"
include "mpteq2dva.mm"
include "wbr.mm"
include "divcnv.mm"
include "adantr.mm"
include "cz.mm"
include "wb.mm"
include "simpr.mm"
include "nnzd.mm"
include "nnex.mm"
include "mptex.mm"
include "eqid.mm"
include "climmpt.mm"
include "sylancl.mm"
include "mpbid.mm"
include "eqbrtrd.mm"

theorem divcnvg
  let cA: class A
  let vn: setvar n
  let cM: class M
  let vm: setvar m

  disjoint A n
  disjoint M n
  disjoint A m
  disjoint m n
  assert |- ( ( A e. CC /\ M e. NN ) -> ( n e. ( ZZ>= ` M ) |-> ( A / n ) ) ~~> 0 )

  proof
    cA
    cc
    wcel
    #
    cM
    cn
    wcel
    #
    wa
    #
    vn
    cM
    cuz
    cfv
    #
    cA
    vn
    cv
    #
    cdiv
    co
    #
    cmpt
    vn
    @3
    @4
    vm
    cn
    cA
    vm
    cv
    #
    cdiv
    co
    #
    cmpt
    #
    cfv
    #
    cmpt
    #
    cc0
    cli
    @2
    vn
    @3
    @5
    @9
    @1
    @4
    @3
    wcel
    #
    @5
    @9
    wceq
    #
    @0
    @1
    @11
    wa
    @4
    cn
    wcel
    #
    @12
    @4
    cM
    eluznn
    @13
    @9
    @5
    @13
    vm
    @4
    @7
    @5
    cn
    @8
    cvv
    @13
    @8
    eqidd
    @6
    @4
    wceq
    @7
    @5
    wceq
    @13
    @6
    @4
    cA
    cdiv
    oveq2
    adantl
    @13
    id
    @13
    cA
    @4
    cdiv
    ovexd
    fvmptd
    eqcomd
    syl
    adantll
    mpteq2dva
    @2
    @8
    cc0
    cli
    wbr
    #
    @10
    cc0
    cli
    wbr
    #
    @0
    @14
    @1
    cA
    vm
    divcnv
    adantr
    @2
    cM
    cz
    wcel
    @8
    cvv
    wcel
    @14
    @15
    wb
    @2
    cM
    @0
    @1
    simpr
    nnzd
    vm
    cn
    @7
    nnex
    mptex
    cc0
    vn
    @8
    @10
    cM
    cvv
    @3
    @3
    eqid
    @10
    eqid
    climmpt
    sylancl
    mpbid
    eqbrtrd
end
