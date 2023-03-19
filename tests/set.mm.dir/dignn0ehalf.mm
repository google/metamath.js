include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cn0.mm"
include "wcel.mm"
include "w3a.mm"
include "c1.mm"
include "caddc.mm"
include "cexp.mm"
include "cfl.mm"
include "cfv.mm"
include "cmo.mm"
include "cdig.mm"
include "cmul.mm"
include "cc.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "wceq.mm"
include "nn0cn.mm"
include "3ad2ant2.mm"
include "2cnne0.mm"
include "a1i.mm"
include "2nn0.mm"
include "id.mm"
include "nn0expcld.mm"
include "nn0cnd.mm"
include "2cnd.mm"
include "2ne0.mm"
include "nn0z.mm"
include "expne0d.mm"
include "jca.mm"
include "3ad2ant3.mm"
include "divdiv1.mm"
include "syl3anc.mm"
include "mulcomd.mm"
include "simp3.mm"
include "expp1d.mm"
include "eqtr4d.mm"
include "oveq2d.mm"
include "eqtr2d.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "cn.mm"
include "cpnf.mm"
include "cico.mm"
include "2nn.mm"
include "peano2nn0.mm"
include "nn0rp0.mm"
include "nn0digval.mm"
include "3ad2ant1.mm"
include "3eqtr4d.mm"

theorem dignn0ehalf
  let cA: class A
  let cI: class I
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( ( A / 2 ) e. NN0 /\ A e. NN0 /\ I e. NN0 ) -> ( ( I + 1 ) ( digit ` 2 ) A ) = ( I ( digit ` 2 ) ( A / 2 ) ) )

  proof
    cA
    c2
    cdiv
    co
    #
    cn0
    wcel
    #
    cA
    cn0
    wcel
    #
    cI
    cn0
    wcel
    #
    w3a
    #
    cA
    c2
    cI
    c1
    caddc
    co
    #
    cexp
    co
    #
    cdiv
    co
    #
    cfl
    cfv
    #
    c2
    cmo
    co
    #
    @0
    c2
    cI
    cexp
    co
    #
    cdiv
    co
    #
    cfl
    cfv
    #
    c2
    cmo
    co
    #
    @5
    cA
    c2
    cdig
    cfv
    #
    co
    #
    cI
    @0
    @14
    co
    #
    @4
    @8
    @12
    c2
    cmo
    @4
    @7
    @11
    cfl
    @4
    @11
    cA
    c2
    @10
    cmul
    co
    #
    cdiv
    co
    #
    @7
    @4
    cA
    cc
    wcel
    #
    c2
    cc
    wcel
    c2
    cc0
    wne
    #
    wa
    #
    @10
    cc
    wcel
    #
    @10
    cc0
    wne
    #
    wa
    #
    @11
    @18
    wceq
    @2
    @1
    @19
    @3
    cA
    nn0cn
    3ad2ant2
    @21
    @4
    2cnne0
    a1i
    @3
    @1
    @24
    @2
    @3
    @22
    @23
    @3
    @10
    @3
    c2
    cI
    c2
    cn0
    wcel
    @3
    2nn0
    a1i
    @3
    id
    nn0expcld
    nn0cnd
    #
    @3
    c2
    cI
    @3
    2cnd
    #
    @20
    @3
    2ne0
    a1i
    cI
    nn0z
    expne0d
    jca
    3ad2ant3
    cA
    c2
    @10
    divdiv1
    syl3anc
    @4
    @17
    @6
    cA
    cdiv
    @4
    @17
    @10
    c2
    cmul
    co
    #
    @6
    @3
    @1
    @17
    @27
    wceq
    @2
    @3
    c2
    @10
    @26
    @25
    mulcomd
    3ad2ant3
    @4
    c2
    cI
    @4
    2cnd
    @1
    @2
    @3
    simp3
    #
    expp1d
    eqtr4d
    oveq2d
    eqtr2d
    fveq2d
    oveq1d
    @4
    c2
    cn
    wcel
    #
    @5
    cn0
    wcel
    #
    cA
    cc0
    cpnf
    cico
    co
    #
    wcel
    #
    @15
    @9
    wceq
    @29
    @4
    2nn
    a1i
    #
    @3
    @1
    @30
    @2
    cI
    peano2nn0
    3ad2ant3
    @2
    @1
    @32
    @3
    cA
    nn0rp0
    3ad2ant2
    c2
    cA
    @5
    nn0digval
    syl3anc
    @4
    @29
    @3
    @0
    @31
    wcel
    #
    @16
    @13
    wceq
    @33
    @28
    @1
    @2
    @34
    @3
    @0
    nn0rp0
    3ad2ant1
    c2
    @0
    cI
    nn0digval
    syl3anc
    3eqtr4d
end
