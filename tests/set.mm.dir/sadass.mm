include "cn0.mm"
include "wss.mm"
include "w3a.mm"
include "csad.mm"
include "co.mm"
include "cv.mm"
include "wcel.mm"
include "sadcl.mm"
include "stoic3.mm"
include "sseld.mm"
include "simp1.mm"
include "3adant1.mm"
include "syl2anc.mm"
include "wb.mm"
include "wa.mm"
include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "cfzo.mm"
include "cin.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpl3.mm"
include "simpr.mm"
include "1nn0.mm"
include "a1i.mm"
include "nn0addcld.mm"
include "sadasslem.mm"
include "eleq2d.mm"
include "elin.mm"
include "3bitr3g.mm"
include "cfz.mm"
include "cuz.mm"
include "cfv.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "eluzfz2.mm"
include "syl.mm"
include "cz.mm"
include "wceq.mm"
include "nn0zd.mm"
include "fzval3.mm"
include "eleqtrd.mm"
include "biantrud.mm"
include "3bitr4d.mm"
include "ex.mm"
include "pm5.21ndd.mm"
include "eqrdv.mm"

theorem sadass
  let cA: class A
  let cB: class B
  let cC: class C
  let vc: setvar c
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let cN: class N


  assert |- ( ( A C_ NN0 /\ B C_ NN0 /\ C C_ NN0 ) -> ( ( A sadd B ) sadd C ) = ( A sadd ( B sadd C ) ) )

  proof
    cA
    cn0
    wss
    #
    cB
    cn0
    wss
    #
    cC
    cn0
    wss
    #
    w3a
    #
    vk
    cA
    cB
    csad
    co
    #
    cC
    csad
    co
    #
    cA
    cB
    cC
    csad
    co
    #
    csad
    co
    #
    @3
    vk
    cv
    #
    cn0
    wcel
    #
    @8
    @5
    wcel
    #
    @8
    @7
    wcel
    #
    @3
    @5
    cn0
    @8
    @0
    @1
    @4
    cn0
    wss
    @2
    @5
    cn0
    wss
    cA
    cB
    sadcl
    @4
    cC
    sadcl
    stoic3
    sseld
    @3
    @7
    cn0
    @8
    @3
    @0
    @6
    cn0
    wss
    #
    @7
    cn0
    wss
    @0
    @1
    @2
    simp1
    @1
    @2
    @12
    @0
    cB
    cC
    sadcl
    3adant1
    cA
    @6
    sadcl
    syl2anc
    sseld
    @3
    @9
    @10
    @11
    wb
    @3
    @9
    wa
    #
    @10
    @8
    cc0
    @8
    c1
    caddc
    co
    #
    cfzo
    co
    #
    wcel
    #
    wa
    #
    @11
    @16
    wa
    #
    @10
    @11
    @13
    @8
    @5
    @15
    cin
    #
    wcel
    @8
    @7
    @15
    cin
    #
    wcel
    @17
    @18
    @13
    @19
    @20
    @8
    @13
    cA
    cB
    cC
    @14
    @0
    @1
    @2
    @9
    simpl1
    @0
    @1
    @2
    @9
    simpl2
    @0
    @1
    @2
    @9
    simpl3
    @13
    @8
    c1
    @3
    @9
    simpr
    #
    c1
    cn0
    wcel
    @13
    1nn0
    a1i
    nn0addcld
    sadasslem
    eleq2d
    @8
    @5
    @15
    elin
    @8
    @7
    @15
    elin
    3bitr3g
    @13
    @16
    @10
    @13
    @8
    cc0
    @8
    cfz
    co
    #
    @15
    @13
    @8
    cc0
    cuz
    cfv
    #
    wcel
    @8
    @22
    wcel
    @13
    @8
    cn0
    @23
    @21
    nn0uz
    syl6eleq
    cc0
    @8
    eluzfz2
    syl
    @13
    @8
    cz
    wcel
    @22
    @15
    wceq
    @13
    @8
    @21
    nn0zd
    cc0
    @8
    fzval3
    syl
    eleqtrd
    #
    biantrud
    @13
    @16
    @11
    @24
    biantrud
    3bitr4d
    ex
    pm5.21ndd
    eqrdv
end
