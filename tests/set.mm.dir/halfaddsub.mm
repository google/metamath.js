include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "cmin.mm"
include "wceq.mm"
include "cmul.mm"
include "ppncan.mm"
include "3anidm13.mm"
include "2times.mm"
include "adantr.mm"
include "eqtr4d.mm"
include "oveq1d.mm"
include "addcl.mm"
include "subcl.mm"
include "cc0.mm"
include "wne.mm"
include "2cnne0.mm"
include "divdir.mm"
include "mp3an3.mm"
include "syl2anc.mm"
include "2cn.mm"
include "2ne0.mm"
include "divcan3.mm"
include "mp3an23.mm"
include "3eqtr3d.mm"
include "pnncan.mm"
include "3anidm23.mm"
include "adantl.mm"
include "divsubdir.mm"
include "jca.mm"

theorem halfaddsub
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( ( ( ( A + B ) / 2 ) + ( ( A - B ) / 2 ) ) = A /\ ( ( ( A + B ) / 2 ) - ( ( A - B ) / 2 ) ) = B ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    wa
    #
    cA
    cB
    caddc
    co
    #
    c2
    cdiv
    co
    #
    cA
    cB
    cmin
    co
    #
    c2
    cdiv
    co
    #
    caddc
    co
    #
    cA
    wceq
    @4
    @6
    cmin
    co
    #
    cB
    wceq
    @2
    @3
    @5
    caddc
    co
    #
    c2
    cdiv
    co
    #
    c2
    cA
    cmul
    co
    #
    c2
    cdiv
    co
    #
    @7
    cA
    @2
    @9
    @11
    c2
    cdiv
    @2
    @9
    cA
    cA
    caddc
    co
    #
    @11
    @0
    @1
    @9
    @13
    wceq
    cA
    cB
    cA
    ppncan
    3anidm13
    @0
    @11
    @13
    wceq
    @1
    cA
    2times
    adantr
    eqtr4d
    oveq1d
    @2
    @3
    cc
    wcel
    #
    @5
    cc
    wcel
    #
    @10
    @7
    wceq
    #
    cA
    cB
    addcl
    #
    cA
    cB
    subcl
    #
    @14
    @15
    c2
    cc
    wcel
    #
    c2
    cc0
    wne
    #
    wa
    #
    @16
    2cnne0
    @3
    @5
    c2
    divdir
    mp3an3
    syl2anc
    @0
    @12
    cA
    wceq
    #
    @1
    @0
    @19
    @20
    @22
    2cn
    2ne0
    cA
    c2
    divcan3
    mp3an23
    adantr
    3eqtr3d
    @2
    @3
    @5
    cmin
    co
    #
    c2
    cdiv
    co
    #
    c2
    cB
    cmul
    co
    #
    c2
    cdiv
    co
    #
    @8
    cB
    @2
    @23
    @25
    c2
    cdiv
    @2
    @23
    cB
    cB
    caddc
    co
    #
    @25
    @0
    @1
    @23
    @27
    wceq
    cA
    cB
    cB
    pnncan
    3anidm23
    @1
    @25
    @27
    wceq
    @0
    cB
    2times
    adantl
    eqtr4d
    oveq1d
    @2
    @14
    @15
    @24
    @8
    wceq
    #
    @17
    @18
    @14
    @15
    @21
    @28
    2cnne0
    @3
    @5
    c2
    divsubdir
    mp3an3
    syl2anc
    @1
    @26
    cB
    wceq
    #
    @0
    @1
    @19
    @20
    @29
    2cn
    2ne0
    cB
    c2
    divcan3
    mp3an23
    adantl
    3eqtr3d
    jca
end
