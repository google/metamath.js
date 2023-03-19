include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cn0.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cdig.mm"
include "cdiv.mm"
include "cfl.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "eluzge2nn0.mm"
include "nn0eo.mm"
include "syl.mm"
include "w3a.mm"
include "dignn0ehalf.mm"
include "syl3an2.mm"
include "wa.mm"
include "cz.mm"
include "eluzelz.mm"
include "nn0z.mm"
include "zefldiv2.mm"
include "syl2anr.mm"
include "eqcomd.mm"
include "3adant3.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "3exp.mm"
include "cexp.mm"
include "cmo.mm"
include "cmin.mm"
include "cn.mm"
include "3ad2ant2.mm"
include "simp2.mm"
include "simp1.mm"
include "nno.mm"
include "syl2anc.mm"
include "simp3.mm"
include "dignn0flhalflem2.mm"
include "syl3anc.mm"
include "oveq1d.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "2nn.mm"
include "a1i.mm"
include "peano2nn0.mm"
include "3ad2ant3.mm"
include "nn0rp0.mm"
include "nn0digval.mm"
include "cr.mm"
include "cle.mm"
include "wbr.mm"
include "eluzelre.mm"
include "rehalfcld.mm"
include "clt.mm"
include "nn0ge0d.mm"
include "2re.mm"
include "2pos.mm"
include "pm3.2i.mm"
include "divge0.mm"
include "syl21anc.mm"
include "flge0nn0.mm"
include "3eqtr4d.mm"
include "jaoi.mm"
include "mpcom.mm"
include "imp.mm"

theorem dignn0flhalf
  let cA: class A
  let cI: class I
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. ( ZZ>= ` 2 ) /\ I e. NN0 ) -> ( ( I + 1 ) ( digit ` 2 ) A ) = ( I ( digit ` 2 ) ( |_ ` ( A / 2 ) ) ) )

  proof
    cA
    c2
    cuz
    cfv
    wcel
    #
    cI
    cn0
    wcel
    #
    cI
    c1
    caddc
    co
    #
    cA
    c2
    cdig
    cfv
    #
    co
    #
    cI
    cA
    c2
    cdiv
    co
    #
    cfl
    cfv
    #
    @3
    co
    #
    wceq
    #
    @5
    cn0
    wcel
    #
    cA
    c1
    caddc
    co
    c2
    cdiv
    co
    cn0
    wcel
    #
    wo
    #
    @0
    @1
    @8
    wi
    #
    @0
    cA
    cn0
    wcel
    #
    @11
    cA
    eluzge2nn0
    #
    cA
    nn0eo
    syl
    @9
    @0
    @12
    wi
    @10
    @9
    @0
    @1
    @8
    @9
    @0
    @1
    w3a
    #
    @4
    cI
    @5
    @3
    co
    #
    @7
    @0
    @9
    @13
    @1
    @4
    @16
    wceq
    @14
    cA
    cI
    dignn0ehalf
    syl3an2
    @15
    @5
    @6
    cI
    @3
    @9
    @0
    @5
    @6
    wceq
    @1
    @9
    @0
    wa
    @6
    @5
    @0
    cA
    cz
    wcel
    #
    @5
    cz
    wcel
    @6
    @5
    wceq
    @9
    c2
    cA
    eluzelz
    #
    @5
    nn0z
    cA
    zefldiv2
    syl2anr
    eqcomd
    3adant3
    oveq2d
    eqtrd
    3exp
    @10
    @0
    @1
    @8
    @10
    @0
    @1
    w3a
    #
    cA
    c2
    @2
    cexp
    co
    cdiv
    co
    cfl
    cfv
    #
    c2
    cmo
    co
    #
    @6
    c2
    cI
    cexp
    co
    cdiv
    co
    cfl
    cfv
    #
    c2
    cmo
    co
    #
    @4
    @7
    @19
    @20
    @22
    c2
    cmo
    @19
    @17
    cA
    c1
    cmin
    co
    c2
    cdiv
    co
    cn
    wcel
    #
    @1
    @20
    @22
    wceq
    @0
    @10
    @17
    @1
    @18
    3ad2ant2
    @19
    @0
    @10
    @24
    @10
    @0
    @1
    simp2
    @10
    @0
    @1
    simp1
    cA
    nno
    syl2anc
    @10
    @0
    @1
    simp3
    #
    cA
    cI
    dignn0flhalflem2
    syl3anc
    oveq1d
    @19
    c2
    cn
    wcel
    #
    @2
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
    @4
    @21
    wceq
    @26
    @19
    2nn
    a1i
    #
    @1
    @10
    @27
    @0
    cI
    peano2nn0
    3ad2ant3
    @0
    @10
    @29
    @1
    @0
    @13
    @29
    @14
    cA
    nn0rp0
    syl
    3ad2ant2
    c2
    cA
    @2
    nn0digval
    syl3anc
    @19
    @26
    @1
    @6
    @28
    wcel
    #
    @7
    @23
    wceq
    @30
    @25
    @19
    @6
    cn0
    wcel
    #
    @31
    @0
    @10
    @32
    @1
    @0
    @5
    cr
    wcel
    cc0
    @5
    cle
    wbr
    #
    @32
    @0
    cA
    c2
    cA
    eluzelre
    #
    rehalfcld
    @0
    cA
    cr
    wcel
    cc0
    cA
    cle
    wbr
    c2
    cr
    wcel
    #
    cc0
    c2
    clt
    wbr
    #
    wa
    #
    @33
    @34
    @0
    cA
    @14
    nn0ge0d
    @37
    @0
    @35
    @36
    2re
    2pos
    pm3.2i
    a1i
    cA
    c2
    divge0
    syl21anc
    @5
    flge0nn0
    syl2anc
    3ad2ant2
    @6
    nn0rp0
    syl
    c2
    @6
    cI
    nn0digval
    syl3anc
    3eqtr4d
    3exp
    jaoi
    mpcom
    imp
end
