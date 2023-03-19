include "cr.mm"
include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "cico.mm"
include "wral.mm"
include "wceq.mm"
include "wreu.mm"
include "wf1o.mm"
include "icoshft.mm"
include "ralrimiv.mm"
include "wa.mm"
include "cmin.mm"
include "cneg.mm"
include "wi.mm"
include "readdcl.mm"
include "3adant2.mm"
include "3adant1.mm"
include "renegcl.mm"
include "3ad2ant3.mm"
include "syl3anc.mm"
include "imp.mm"
include "cxr.mm"
include "wss.mm"
include "rexrd.mm"
include "icossre.mm"
include "syl2anc.mm"
include "sselda.mm"
include "recnd.mm"
include "simpl3.mm"
include "negsubd.mm"
include "simp3.mm"
include "simp1.mm"
include "pncand.mm"
include "eqtrd.mm"
include "simp2.mm"
include "oveq12d.mm"
include "adantr.mm"
include "3eltr3d.mm"
include "reueq.mm"
include "sylib.mm"
include "simpll3.mm"
include "simpl1.mm"
include "simpl2.mm"
include "subadd2d.mm"
include "eqcom.mm"
include "3bitr4g.mm"
include "reubidva.mm"
include "mpbid.mm"
include "ralrimiva.mm"
include "f1ompt.mm"
include "sylanbrc.mm"

theorem icoshftf1o
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vy: setvar y
  assume icoshftf1o.1: |- F = ( x e. ( A [,) B ) |-> ( x + C ) )

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint C y
  disjoint F y
  assert |- ( ( A e. RR /\ B e. RR /\ C e. RR ) -> F : ( A [,) B ) -1-1-onto-> ( ( A + C ) [,) ( B + C ) ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cC
    cr
    wcel
    #
    w3a
    #
    vx
    cv
    #
    cC
    caddc
    co
    #
    cA
    cC
    caddc
    co
    #
    cB
    cC
    caddc
    co
    #
    cico
    co
    #
    wcel
    #
    vx
    cA
    cB
    cico
    co
    #
    wral
    vy
    cv
    #
    @5
    wceq
    #
    vx
    @10
    wreu
    #
    vy
    @8
    wral
    @10
    @8
    cF
    wf1o
    @3
    @9
    vx
    @10
    cA
    cB
    cC
    @4
    icoshft
    ralrimiv
    @3
    @13
    vy
    @8
    @3
    @11
    @8
    wcel
    #
    wa
    #
    @4
    @11
    cC
    cmin
    co
    #
    wceq
    #
    vx
    @10
    wreu
    #
    @13
    @15
    @16
    @10
    wcel
    @18
    @15
    @11
    cC
    cneg
    #
    caddc
    co
    #
    @6
    @19
    caddc
    co
    #
    @7
    @19
    caddc
    co
    #
    cico
    co
    #
    @16
    @10
    @3
    @14
    @20
    @23
    wcel
    #
    @3
    @6
    cr
    wcel
    #
    @7
    cr
    wcel
    #
    @19
    cr
    wcel
    #
    @14
    @24
    wi
    @0
    @2
    @25
    @1
    cA
    cC
    readdcl
    3adant2
    #
    @1
    @2
    @26
    @0
    cB
    cC
    readdcl
    3adant1
    #
    @2
    @0
    @27
    @1
    cC
    renegcl
    3ad2ant3
    @6
    @7
    @19
    @11
    icoshft
    syl3anc
    imp
    @15
    @11
    cC
    @15
    @11
    @3
    @8
    cr
    @11
    @3
    @25
    @7
    cxr
    wcel
    @8
    cr
    wss
    @28
    @3
    @7
    @29
    rexrd
    @6
    @7
    icossre
    syl2anc
    sselda
    #
    recnd
    @15
    cC
    @0
    @1
    @2
    @14
    simpl3
    recnd
    negsubd
    @3
    @23
    @10
    wceq
    @14
    @3
    @21
    cA
    @22
    cB
    cico
    @3
    @21
    @6
    cC
    cmin
    co
    cA
    @3
    @6
    cC
    @3
    @6
    @28
    recnd
    @3
    cC
    @0
    @1
    @2
    simp3
    recnd
    #
    negsubd
    @3
    cA
    cC
    @3
    cA
    @0
    @1
    @2
    simp1
    recnd
    @31
    pncand
    eqtrd
    @3
    @22
    @7
    cC
    cmin
    co
    cB
    @3
    @7
    cC
    @3
    @7
    @29
    recnd
    @31
    negsubd
    @3
    cB
    cC
    @3
    cB
    @0
    @1
    @2
    simp2
    recnd
    @31
    pncand
    eqtrd
    oveq12d
    adantr
    3eltr3d
    vx
    @10
    @16
    reueq
    sylib
    @15
    @17
    @12
    vx
    @10
    @15
    @4
    @10
    wcel
    #
    wa
    #
    @16
    @4
    wceq
    @5
    @11
    wceq
    @17
    @12
    @33
    @11
    cC
    @4
    @33
    @11
    @15
    @11
    cr
    wcel
    @32
    @30
    adantr
    recnd
    @33
    cC
    @0
    @1
    @2
    @14
    @32
    simpll3
    recnd
    @33
    @4
    @15
    @10
    cr
    @4
    @15
    @0
    cB
    cxr
    wcel
    @10
    cr
    wss
    @0
    @1
    @2
    @14
    simpl1
    @15
    cB
    @0
    @1
    @2
    @14
    simpl2
    rexrd
    cA
    cB
    icossre
    syl2anc
    sselda
    recnd
    subadd2d
    @4
    @16
    eqcom
    @11
    @5
    eqcom
    3bitr4g
    reubidva
    mpbid
    ralrimiva
    vx
    vy
    @10
    @8
    @5
    cF
    icoshftf1o.1
    f1ompt
    sylanbrc
end
