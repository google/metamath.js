include "cc.mm"
include "wss.mm"
include "wcel.mm"
include "cn0.mm"
include "w3a.mm"
include "cc0.mm"
include "csn.mm"
include "cun.mm"
include "cply.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "wceq.mm"
include "cif.mm"
include "cexp.mm"
include "cmul.mm"
include "csu.mm"
include "cmpt.mm"
include "ssel2.mm"
include "ply1termlem.mm"
include "stoic3.mm"
include "simp1.mm"
include "0cnd.mm"
include "snssd.mm"
include "unssd.mm"
include "simp3.mm"
include "wa.mm"
include "simpl2.mm"
include "elun1.mm"
include "syl.mm"
include "ssun2.mm"
include "c0ex.mm"
include "snss.mm"
include "mpbir.mm"
include "ifcl.mm"
include "sylancl.mm"
include "elplyd.mm"
include "eqeltrd.mm"
include "plyun0.mm"
include "syl6eleq.mm"

theorem ply1term
  let vz: setvar z
  let cA: class A
  let cS: class S
  let cF: class F
  let cN: class N
  let vk: setvar k
  assume ply1term.1: |- F = ( z e. CC |-> ( A x. ( z ^ N ) ) )

  disjoint A z
  disjoint N z
  disjoint S z
  disjoint k z
  disjoint A k
  disjoint N k
  disjoint S k
  assert |- ( ( S C_ CC /\ A e. S /\ N e. NN0 ) -> F e. ( Poly ` S ) )

  proof
    cS
    cc
    wss
    #
    cA
    cS
    wcel
    #
    cN
    cn0
    wcel
    #
    w3a
    #
    cF
    cS
    cc0
    csn
    #
    cun
    #
    cply
    cfv
    #
    cS
    cply
    cfv
    @3
    cF
    vz
    cc
    cc0
    cN
    cfz
    co
    #
    vk
    cv
    #
    cN
    wceq
    #
    cA
    cc0
    cif
    #
    vz
    cv
    @8
    cexp
    co
    cmul
    co
    vk
    csu
    cmpt
    #
    @6
    @0
    @1
    cA
    cc
    wcel
    @2
    cF
    @11
    wceq
    cS
    cc
    cA
    ssel2
    vz
    cA
    vk
    cF
    cN
    ply1term.1
    ply1termlem
    stoic3
    @3
    vz
    @10
    @5
    vk
    cN
    @3
    cS
    @4
    cc
    @0
    @1
    @2
    simp1
    @3
    cc0
    cc
    @3
    0cnd
    snssd
    unssd
    @0
    @1
    @2
    simp3
    @3
    @8
    @7
    wcel
    #
    wa
    #
    cA
    @5
    wcel
    #
    cc0
    @5
    wcel
    #
    @10
    @5
    wcel
    @13
    @1
    @14
    @0
    @1
    @2
    @12
    simpl2
    cA
    cS
    @4
    elun1
    syl
    @15
    @4
    @5
    wss
    @4
    cS
    ssun2
    cc0
    @5
    c0ex
    snss
    mpbir
    @9
    cA
    cc0
    @5
    ifcl
    sylancl
    elplyd
    eqeltrd
    cS
    plyun0
    syl6eleq
end
