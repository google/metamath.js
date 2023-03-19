include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cz.mm"
include "w3a.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "cdiv.mm"
include "expclz.mm"
include "reccl.mm"
include "3adant3.mm"
include "recne0.mm"
include "simp3.mm"
include "syl3anc.mm"
include "expne0i.mm"
include "cmul.mm"
include "simp1.mm"
include "simp2.mm"
include "recidd.mm"
include "oveq1d.mm"
include "wceq.mm"
include "mulexpz.mm"
include "syl221anc.mm"
include "1exp.mm"
include "syl.mm"
include "3eqtr3d.mm"
include "mvllmuld.mm"

theorem exprec
  let cA: class A
  let cN: class N
  let vj: setvar j
  let vk: setvar k
  let cB: class B
  let cM: class M


  assert |- ( ( A e. CC /\ A =/= 0 /\ N e. ZZ ) -> ( ( 1 / A ) ^ N ) = ( 1 / ( A ^ N ) ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    cN
    cz
    wcel
    #
    w3a
    #
    cA
    cN
    cexp
    co
    #
    c1
    cA
    cdiv
    co
    #
    cN
    cexp
    co
    #
    c1
    cA
    cN
    expclz
    @3
    @5
    cc
    wcel
    #
    @5
    cc0
    wne
    #
    @2
    @6
    cc
    wcel
    @0
    @1
    @7
    @2
    cA
    reccl
    3adant3
    #
    @0
    @1
    @8
    @2
    cA
    recne0
    3adant3
    #
    @0
    @1
    @2
    simp3
    #
    @5
    cN
    expclz
    syl3anc
    cA
    cN
    expne0i
    @3
    cA
    @5
    cmul
    co
    #
    cN
    cexp
    co
    #
    c1
    cN
    cexp
    co
    #
    @4
    @6
    cmul
    co
    #
    c1
    @3
    @12
    c1
    cN
    cexp
    @3
    cA
    @0
    @1
    @2
    simp1
    #
    @0
    @1
    @2
    simp2
    #
    recidd
    oveq1d
    @3
    @0
    @1
    @7
    @8
    @2
    @13
    @15
    wceq
    @16
    @17
    @9
    @10
    @11
    cA
    @5
    cN
    mulexpz
    syl221anc
    @3
    @2
    @14
    c1
    wceq
    @11
    cN
    1exp
    syl
    3eqtr3d
    mvllmuld
end
