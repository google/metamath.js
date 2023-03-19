include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "w3a.mm"
include "cn0.mm"
include "wa.mm"
include "cexp.mm"
include "co.mm"
include "cuz.mm"
include "cfv.mm"
include "simpl1.mm"
include "0nn0.mm"
include "a1i.mm"
include "simpr.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "simpl2.mm"
include "simpl3.mm"
include "leexp2r.mm"
include "syl32anc.mm"
include "cc.mm"
include "wceq.mm"
include "recnd.mm"
include "exp0.mm"
include "syl.mm"
include "breqtrd.mm"

theorem exple1
  let cA: class A
  let cN: class N


  assert |- ( ( ( A e. RR /\ 0 <_ A /\ A <_ 1 ) /\ N e. NN0 ) -> ( A ^ N ) <_ 1 )

  proof
    cA
    cr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    cA
    c1
    cle
    wbr
    #
    w3a
    #
    cN
    cn0
    wcel
    #
    wa
    #
    cA
    cN
    cexp
    co
    #
    cA
    cc0
    cexp
    co
    #
    c1
    cle
    @5
    @0
    cc0
    cn0
    wcel
    #
    cN
    cc0
    cuz
    cfv
    #
    wcel
    @1
    @2
    @6
    @7
    cle
    wbr
    @0
    @1
    @2
    @4
    simpl1
    #
    @8
    @5
    0nn0
    a1i
    @5
    cN
    cn0
    @9
    @3
    @4
    simpr
    nn0uz
    syl6eleq
    @0
    @1
    @2
    @4
    simpl2
    @0
    @1
    @2
    @4
    simpl3
    cA
    cc0
    cN
    leexp2r
    syl32anc
    @5
    cA
    cc
    wcel
    @7
    c1
    wceq
    @5
    cA
    @10
    recnd
    cA
    exp0
    syl
    breqtrd
end
