include "cn.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "cdiv.mm"
include "co.mm"
include "wa.mm"
include "caddc.mm"
include "wceq.mm"
include "cc.mm"
include "cc0.mm"
include "wne.mm"
include "zcn.mm"
include "nncn.mm"
include "nnne0.mm"
include "jca.mm"
include "divdir.mm"
include "syl3an.mm"
include "3comr.mm"
include "adantr.mm"
include "zaddcl.mm"
include "adantl.mm"
include "eqeltrd.mm"

theorem zdivadd
  let cA: class A
  let cB: class B
  let cD: class D


  assert |- ( ( ( D e. NN /\ A e. ZZ /\ B e. ZZ ) /\ ( ( A / D ) e. ZZ /\ ( B / D ) e. ZZ ) ) -> ( ( A + B ) / D ) e. ZZ )

  proof
    cD
    cn
    wcel
    #
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    w3a
    #
    cA
    cD
    cdiv
    co
    #
    cz
    wcel
    cB
    cD
    cdiv
    co
    #
    cz
    wcel
    wa
    #
    wa
    cA
    cB
    caddc
    co
    cD
    cdiv
    co
    #
    @4
    @5
    caddc
    co
    #
    cz
    @3
    @7
    @8
    wceq
    #
    @6
    @1
    @2
    @0
    @9
    @1
    cA
    cc
    wcel
    @2
    cB
    cc
    wcel
    @0
    cD
    cc
    wcel
    #
    cD
    cc0
    wne
    #
    wa
    @9
    cA
    zcn
    cB
    zcn
    @0
    @10
    @11
    cD
    nncn
    cD
    nnne0
    jca
    cA
    cB
    cD
    divdir
    syl3an
    3comr
    adantr
    @6
    @8
    cz
    wcel
    @3
    @4
    @5
    zaddcl
    adantl
    eqeltrd
end
