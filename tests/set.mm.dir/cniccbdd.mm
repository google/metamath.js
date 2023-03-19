include "cr.mm"
include "wcel.mm"
include "cicc.mm"
include "co.mm"
include "cc.mm"
include "ccncf.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "clt.mm"
include "wa.mm"
include "cc0.mm"
include "0re.mm"
include "c0.mm"
include "ral0.mm"
include "wceq.mm"
include "cxr.mm"
include "wb.mm"
include "simp1.mm"
include "rexrd.mm"
include "simp2.mm"
include "icc0.mm"
include "syl2anc.mm"
include "biimpar.mm"
include "raleqdv.mm"
include "mpbiri.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "sylancr.mm"
include "ccom.mm"
include "adantr.mm"
include "simpr.mm"
include "simp3.mm"
include "abscncf.mm"
include "a1i.mm"
include "cncfco.mm"
include "evthicc.mm"
include "simpld.mm"
include "wf.mm"
include "cncff.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "fvco3.mm"
include "sylan.mm"
include "breq1d.mm"
include "ralbidva.mm"
include "biimpd.mm"
include "syl6an.mm"
include "rexlimdva.mm"
include "imp.mm"
include "syldan.mm"
include "ltlecasei.mm"

theorem cniccbdd
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let vz: setvar z

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint F x
  disjoint F y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint F z
  assert |- ( ( A e. RR /\ B e. RR /\ F e. ( ( A [,] B ) -cn-> CC ) ) -> E. x e. RR A. y e. ( A [,] B ) ( abs ` ( F ` y ) ) <_ x )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cF
    cA
    cB
    cicc
    co
    #
    cc
    ccncf
    co
    wcel
    #
    w3a
    #
    vy
    cv
    #
    cF
    cfv
    cabs
    cfv
    #
    vx
    cv
    #
    cle
    wbr
    #
    vy
    @2
    wral
    #
    vx
    cr
    wrex
    #
    cB
    cA
    @4
    cB
    cA
    clt
    wbr
    #
    wa
    #
    cc0
    cr
    wcel
    @6
    cc0
    cle
    wbr
    #
    vy
    @2
    wral
    #
    @10
    0re
    @12
    @14
    @13
    vy
    c0
    wral
    @13
    vy
    ral0
    @12
    @13
    vy
    @2
    c0
    @4
    @2
    c0
    wceq
    #
    @11
    @4
    cA
    cxr
    wcel
    cB
    cxr
    wcel
    @15
    @11
    wb
    @4
    cA
    @0
    @1
    @3
    simp1
    #
    rexrd
    @4
    cB
    @0
    @1
    @3
    simp2
    #
    rexrd
    cA
    cB
    icc0
    syl2anc
    biimpar
    raleqdv
    mpbiri
    @9
    @14
    vx
    cc0
    cr
    @7
    cc0
    wceq
    @8
    @13
    vy
    @2
    @7
    cc0
    @6
    cle
    breq2
    ralbidv
    rspcev
    sylancr
    @4
    cA
    cB
    cle
    wbr
    #
    @5
    cabs
    cF
    ccom
    #
    cfv
    #
    vz
    cv
    #
    @19
    cfv
    #
    cle
    wbr
    #
    vy
    @2
    wral
    #
    vz
    @2
    wrex
    #
    @10
    @4
    @18
    wa
    #
    @25
    @22
    @20
    cle
    wbr
    vy
    @2
    wral
    vz
    @2
    wrex
    @26
    vz
    vy
    vz
    vy
    cA
    cB
    @19
    @4
    @0
    @18
    @16
    adantr
    @4
    @1
    @18
    @17
    adantr
    @4
    @18
    simpr
    @4
    @19
    @2
    cr
    ccncf
    co
    wcel
    #
    @18
    @4
    @2
    cc
    cr
    cF
    cabs
    @0
    @1
    @3
    simp3
    #
    cabs
    cc
    cr
    ccncf
    co
    wcel
    @4
    abscncf
    a1i
    cncfco
    #
    adantr
    evthicc
    simpld
    @4
    @25
    @10
    @4
    @24
    @10
    vz
    @2
    @4
    @21
    @2
    wcel
    #
    wa
    #
    @22
    cr
    wcel
    @24
    @6
    @22
    cle
    wbr
    #
    vy
    @2
    wral
    #
    @10
    @4
    @2
    cr
    @21
    @19
    @4
    @27
    @2
    cr
    @19
    wf
    @29
    @2
    cr
    @19
    cncff
    syl
    ffvelrnda
    @31
    @24
    @33
    @31
    @23
    @32
    vy
    @2
    @31
    @5
    @2
    wcel
    #
    wa
    @20
    @6
    @22
    cle
    @31
    @2
    cc
    cF
    wf
    #
    @34
    @20
    @6
    wceq
    @4
    @35
    @30
    @4
    @3
    @35
    @28
    @2
    cc
    cF
    cncff
    syl
    adantr
    @2
    cc
    @5
    cabs
    cF
    fvco3
    sylan
    breq1d
    ralbidva
    biimpd
    @9
    @33
    vx
    @22
    cr
    @7
    @22
    wceq
    @8
    @32
    vy
    @2
    @7
    @22
    @6
    cle
    breq2
    ralbidv
    rspcev
    syl6an
    rexlimdva
    imp
    syldan
    @17
    @16
    ltlecasei
end
