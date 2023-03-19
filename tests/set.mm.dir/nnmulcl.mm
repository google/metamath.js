include "cn.mm"
include "wcel.mm"
include "cmul.mm"
include "co.mm"
include "cv.mm"
include "wi.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "imbi2d.mm"
include "cc.mm"
include "nncn.mm"
include "mulid1.mm"
include "biimprd.mm"
include "mpcom.mm"
include "wa.mm"
include "nnaddcl.mm"
include "ancoms.mm"
include "ax-1cn.mm"
include "adddi.mm"
include "mp3an3.mm"
include "oveq2d.mm"
include "adantr.mm"
include "eqtrd.mm"
include "syl2an.mm"
include "syl5ibr.mm"
include "exp4b.mm"
include "pm2.43b.mm"
include "a2d.mm"
include "nnind.mm"
include "impcom.mm"

theorem nnmulcl
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. NN /\ B e. NN ) -> ( A x. B ) e. NN )

  proof
    cB
    cn
    wcel
    cA
    cn
    wcel
    #
    cA
    cB
    cmul
    co
    #
    cn
    wcel
    #
    @0
    cA
    vx
    cv
    #
    cmul
    co
    #
    cn
    wcel
    #
    wi
    @0
    cA
    c1
    cmul
    co
    #
    cn
    wcel
    #
    wi
    @0
    cA
    vy
    cv
    #
    cmul
    co
    #
    cn
    wcel
    #
    wi
    @0
    cA
    @8
    c1
    caddc
    co
    #
    cmul
    co
    #
    cn
    wcel
    #
    wi
    @0
    @2
    wi
    vx
    vy
    cB
    @3
    c1
    wceq
    #
    @5
    @7
    @0
    @14
    @4
    @6
    cn
    @3
    c1
    cA
    cmul
    oveq2
    eleq1d
    imbi2d
    @3
    @8
    wceq
    #
    @5
    @10
    @0
    @15
    @4
    @9
    cn
    @3
    @8
    cA
    cmul
    oveq2
    eleq1d
    imbi2d
    @3
    @11
    wceq
    #
    @5
    @13
    @0
    @16
    @4
    @12
    cn
    @3
    @11
    cA
    cmul
    oveq2
    eleq1d
    imbi2d
    @3
    cB
    wceq
    #
    @5
    @2
    @0
    @17
    @4
    @1
    cn
    @3
    cB
    cA
    cmul
    oveq2
    eleq1d
    imbi2d
    cA
    cc
    wcel
    #
    @0
    @7
    cA
    nncn
    #
    @18
    @7
    @0
    @18
    @6
    cA
    cn
    cA
    mulid1
    #
    eleq1d
    biimprd
    mpcom
    @8
    cn
    wcel
    #
    @0
    @10
    @13
    @21
    @0
    @10
    @13
    wi
    @0
    @21
    @0
    @10
    @13
    @0
    @10
    wa
    @13
    @0
    @21
    wa
    #
    @9
    cA
    caddc
    co
    #
    cn
    wcel
    #
    @10
    @0
    @24
    @9
    cA
    nnaddcl
    ancoms
    @22
    @12
    @23
    cn
    @0
    @18
    @8
    cc
    wcel
    #
    @12
    @23
    wceq
    @21
    @19
    @8
    nncn
    @18
    @25
    wa
    @12
    @9
    @6
    caddc
    co
    #
    @23
    @18
    @25
    c1
    cc
    wcel
    @12
    @26
    wceq
    ax-1cn
    cA
    @8
    c1
    adddi
    mp3an3
    @18
    @26
    @23
    wceq
    @25
    @18
    @6
    cA
    @9
    caddc
    @20
    oveq2d
    adantr
    eqtrd
    syl2an
    eleq1d
    syl5ibr
    exp4b
    pm2.43b
    a2d
    nnind
    impcom
end
