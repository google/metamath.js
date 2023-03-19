include "cn.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "cv.mm"
include "wi.mm"
include "c1.mm"
include "wceq.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "imbi2d.mm"
include "peano2nn.mm"
include "wa.mm"
include "cc.mm"
include "nncn.mm"
include "ax-1cn.mm"
include "addass.mm"
include "mp3an3.mm"
include "syl2an.mm"
include "syl5ib.mm"
include "expcom.mm"
include "a2d.mm"
include "nnind.mm"
include "impcom.mm"

theorem nnaddcl
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. NN /\ B e. NN ) -> ( A + B ) e. NN )

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
    caddc
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
    caddc
    co
    #
    cn
    wcel
    #
    wi
    @0
    cA
    c1
    caddc
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
    caddc
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
    caddc
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
    caddc
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
    caddc
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
    caddc
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
    caddc
    oveq2
    eleq1d
    imbi2d
    cA
    peano2nn
    @8
    cn
    wcel
    #
    @0
    @10
    @13
    @0
    @18
    @10
    @13
    wi
    @10
    @9
    c1
    caddc
    co
    #
    cn
    wcel
    @0
    @18
    wa
    #
    @13
    @9
    peano2nn
    @20
    @19
    @12
    cn
    @0
    cA
    cc
    wcel
    #
    @8
    cc
    wcel
    #
    @19
    @12
    wceq
    #
    @18
    cA
    nncn
    @8
    nncn
    @21
    @22
    c1
    cc
    wcel
    @23
    ax-1cn
    cA
    @8
    c1
    addass
    mp3an3
    syl2an
    eleq1d
    syl5ib
    expcom
    a2d
    nnind
    impcom
end
