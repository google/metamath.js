include "cr.mm"
include "wcel.mm"
include "cn0.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cneg.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cexp.mm"
include "cmin.mm"
include "renegcl.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "wa.mm"
include "simpr.mm"
include "simpl.mm"
include "1red.mm"
include "lenegd.mm"
include "mpbid.mm"
include "3adant2.mm"
include "bernneq.mm"
include "syl3anc.mm"
include "cc.mm"
include "wceq.mm"
include "recn.mm"
include "nn0cn.mm"
include "3ad2ant2.mm"
include "1cnd.mm"
include "mulneg1.mm"
include "oveq2d.mm"
include "3adant3.mm"
include "simp3.mm"
include "mulcl.mm"
include "negsubd.mm"
include "mulcom.mm"
include "3eqtrd.mm"
include "oveq1d.mm"
include "3brtr3d.mm"

theorem stoweidlem10
  let cA: class A
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. RR /\ N e. NN0 /\ A <_ 1 ) -> ( 1 - ( N x. A ) ) <_ ( ( 1 - A ) ^ N ) )

  proof
    cA
    cr
    wcel
    #
    cN
    cn0
    wcel
    #
    cA
    c1
    cle
    wbr
    #
    w3a
    #
    c1
    cA
    cneg
    #
    cN
    cmul
    co
    #
    caddc
    co
    #
    c1
    @4
    caddc
    co
    #
    cN
    cexp
    co
    #
    c1
    cN
    cA
    cmul
    co
    #
    cmin
    co
    #
    c1
    cA
    cmin
    co
    #
    cN
    cexp
    co
    #
    cle
    @3
    @4
    cr
    wcel
    #
    @1
    c1
    cneg
    @4
    cle
    wbr
    #
    @6
    @8
    cle
    wbr
    @0
    @1
    @13
    @2
    cA
    renegcl
    3ad2ant1
    @0
    @1
    @2
    simp2
    @0
    @2
    @14
    @1
    @0
    @2
    wa
    #
    @2
    @14
    @0
    @2
    simpr
    @15
    cA
    c1
    @0
    @2
    simpl
    @15
    1red
    lenegd
    mpbid
    3adant2
    @4
    cN
    bernneq
    syl3anc
    @3
    cA
    cc
    wcel
    #
    cN
    cc
    wcel
    #
    c1
    cc
    wcel
    #
    @6
    @10
    wceq
    @0
    @1
    @16
    @2
    cA
    recn
    #
    3ad2ant1
    @1
    @0
    @17
    @2
    cN
    nn0cn
    3ad2ant2
    @3
    1cnd
    @16
    @17
    @18
    w3a
    #
    @6
    c1
    cA
    cN
    cmul
    co
    #
    cneg
    #
    caddc
    co
    #
    c1
    @21
    cmin
    co
    #
    @10
    @16
    @17
    @6
    @23
    wceq
    @18
    @16
    @17
    wa
    #
    @5
    @22
    c1
    caddc
    cA
    cN
    mulneg1
    oveq2d
    3adant3
    @20
    c1
    @21
    @16
    @17
    @18
    simp3
    @16
    @17
    @21
    cc
    wcel
    @18
    cA
    cN
    mulcl
    3adant3
    negsubd
    @16
    @17
    @24
    @10
    wceq
    @18
    @25
    @21
    @9
    c1
    cmin
    cA
    cN
    mulcom
    oveq2d
    3adant3
    3eqtrd
    syl3anc
    @0
    @1
    @8
    @12
    wceq
    @2
    @0
    @7
    @11
    cN
    cexp
    @0
    c1
    cA
    @0
    1cnd
    @19
    negsubd
    oveq1d
    3ad2ant1
    3brtr3d
end
