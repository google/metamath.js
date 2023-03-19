include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "cvv.mm"
include "cn0.mm"
include "nn0uz.mm"
include "0zd.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "cfa.mm"
include "cfv.mm"
include "cdiv.mm"
include "cmpt.mm"
include "nn0ex.mm"
include "mptex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "efcllem.mm"
include "wa.mm"
include "wceq.mm"
include "simpr.mm"
include "eftcl.mm"
include "oveq2.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "adantl.mm"
include "simpl.mm"
include "fvmptd.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "serf0.mm"

theorem expfac
  let cA: class A
  let vn: setvar n
  let cF: class F
  let vm: setvar m
  assume expfac.f: |- F = ( n e. NN0 |-> ( ( A ^ n ) / ( ! ` n ) ) )

  disjoint A n
  disjoint A m
  disjoint m n
  disjoint F m
  assert |- ( A e. CC -> F ~~> 0 )

  proof
    cA
    cc
    wcel
    #
    vm
    cF
    cc0
    cvv
    cn0
    nn0uz
    @0
    0zd
    cF
    cvv
    wcel
    @0
    cF
    vn
    cn0
    cA
    vn
    cv
    #
    cexp
    co
    #
    @1
    cfa
    cfv
    #
    cdiv
    co
    #
    cmpt
    #
    cvv
    expfac.f
    vn
    cn0
    @4
    nn0ex
    mptex
    eqeltri
    a1i
    cA
    vn
    cF
    expfac.f
    efcllem
    @0
    vm
    cv
    #
    cn0
    wcel
    #
    wa
    #
    @6
    cF
    cfv
    #
    cA
    @6
    cexp
    co
    #
    @6
    cfa
    cfv
    #
    cdiv
    co
    #
    cc
    @8
    @7
    @12
    cc
    wcel
    #
    @9
    @12
    wceq
    @0
    @7
    simpr
    cA
    @6
    eftcl
    #
    @7
    @13
    wa
    #
    vn
    @6
    @4
    @12
    cn0
    cF
    cc
    cF
    @5
    wceq
    @15
    expfac.f
    a1i
    @1
    @6
    wceq
    #
    @4
    @12
    wceq
    @15
    @16
    @2
    @10
    @3
    @11
    cdiv
    @1
    @6
    cA
    cexp
    oveq2
    @1
    @6
    cfa
    fveq2
    oveq12d
    adantl
    @7
    @13
    simpl
    @7
    @13
    simpr
    fvmptd
    syl2anc
    @14
    eqeltrd
    serf0
end
