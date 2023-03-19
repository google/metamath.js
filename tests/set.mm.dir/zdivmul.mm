include "cn.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "cdiv.mm"
include "co.mm"
include "wa.mm"
include "cmul.mm"
include "wceq.mm"
include "cc.mm"
include "cc0.mm"
include "wne.mm"
include "zcn.mm"
include "3ad2ant2.mm"
include "3ad2ant1.mm"
include "nncn.mm"
include "nnne0.mm"
include "jca.mm"
include "3ad2ant3.mm"
include "divass.mm"
include "syl3anc.mm"
include "3comr.mm"
include "adantr.mm"
include "zmulcl.mm"
include "3ad2antl3.mm"
include "eqeltrd.mm"

theorem zdivmul
  let cA: class A
  let cB: class B
  let cD: class D


  assert |- ( ( ( D e. NN /\ A e. ZZ /\ B e. ZZ ) /\ ( A / D ) e. ZZ ) -> ( ( B x. A ) / D ) e. ZZ )

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
    #
    wa
    cB
    cA
    cmul
    co
    cD
    cdiv
    co
    #
    cB
    @4
    cmul
    co
    #
    cz
    @3
    @6
    @7
    wceq
    #
    @5
    @1
    @2
    @0
    @8
    @1
    @2
    @0
    w3a
    cB
    cc
    wcel
    #
    cA
    cc
    wcel
    #
    cD
    cc
    wcel
    #
    cD
    cc0
    wne
    #
    wa
    #
    @8
    @2
    @1
    @9
    @0
    cB
    zcn
    3ad2ant2
    @1
    @2
    @10
    @0
    cA
    zcn
    3ad2ant1
    @0
    @1
    @13
    @2
    @0
    @11
    @12
    cD
    nncn
    cD
    nnne0
    jca
    3ad2ant3
    cB
    cA
    cD
    divass
    syl3anc
    3comr
    adantr
    @2
    @0
    @5
    @7
    cz
    wcel
    @1
    cB
    @4
    zmulcl
    3ad2antl3
    eqeltrd
end
