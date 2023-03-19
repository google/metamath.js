include "cz.mm"
include "wcel.mm"
include "cabs.mm"
include "cfv.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "zmulcl.mm"
include "ad2ant2r.mm"
include "wceq.mm"
include "cc.mm"
include "zcn.mm"
include "absmul.mm"
include "syl2an.mm"
include "cr.mm"
include "cc0.mm"
include "wi.mm"
include "abscl.mm"
include "absge0.mm"
include "jca.mm"
include "syl.mm"
include "adantr.mm"
include "1red.mm"
include "adantl.mm"
include "lemul12a.mm"
include "syl22anc.mm"
include "imp.mm"
include "an4s.mm"
include "1t1e1.mm"
include "syl6breq.mm"
include "eqbrtrd.mm"
include "cv.mm"
include "fveq2.mm"
include "breq1d.mm"
include "elrab2.mm"
include "anbi12i.mm"
include "3imtr4i.mm"

theorem lgslem3
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cZ: class Z
  assume lgslem2.z: |- Z = { x e. ZZ | ( abs ` x ) <_ 1 }

  disjoint A x
  disjoint B x
  assert |- ( ( A e. Z /\ B e. Z ) -> ( A x. B ) e. Z )

  proof
    cA
    cz
    wcel
    #
    cA
    cabs
    cfv
    #
    c1
    cle
    wbr
    #
    wa
    #
    cB
    cz
    wcel
    #
    cB
    cabs
    cfv
    #
    c1
    cle
    wbr
    #
    wa
    #
    wa
    #
    cA
    cB
    cmul
    co
    #
    cz
    wcel
    #
    @9
    cabs
    cfv
    #
    c1
    cle
    wbr
    #
    wa
    cA
    cZ
    wcel
    #
    cB
    cZ
    wcel
    #
    wa
    @9
    cZ
    wcel
    @8
    @10
    @12
    @0
    @4
    @10
    @2
    @6
    cA
    cB
    zmulcl
    ad2ant2r
    @8
    @11
    @1
    @5
    cmul
    co
    #
    c1
    cle
    @0
    @4
    @11
    @15
    wceq
    #
    @2
    @6
    @0
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    @16
    @4
    cA
    zcn
    #
    cB
    zcn
    #
    cA
    cB
    absmul
    syl2an
    ad2ant2r
    @8
    @15
    c1
    c1
    cmul
    co
    #
    c1
    cle
    @0
    @4
    @2
    @6
    @15
    @21
    cle
    wbr
    #
    @0
    @4
    wa
    #
    @2
    @6
    wa
    #
    @22
    @23
    @1
    cr
    wcel
    #
    cc0
    @1
    cle
    wbr
    #
    wa
    #
    c1
    cr
    wcel
    #
    @5
    cr
    wcel
    #
    cc0
    @5
    cle
    wbr
    #
    wa
    #
    @28
    @24
    @22
    wi
    @0
    @27
    @4
    @0
    @17
    @27
    @19
    @17
    @25
    @26
    cA
    abscl
    cA
    absge0
    jca
    syl
    adantr
    @23
    1red
    #
    @4
    @31
    @0
    @4
    @18
    @31
    @20
    @18
    @29
    @30
    cB
    abscl
    cB
    absge0
    jca
    syl
    adantl
    @32
    @1
    c1
    @5
    c1
    lemul12a
    syl22anc
    imp
    an4s
    1t1e1
    syl6breq
    eqbrtrd
    jca
    @13
    @3
    @14
    @7
    vx
    cv
    #
    cabs
    cfv
    #
    c1
    cle
    wbr
    #
    @2
    vx
    cA
    cz
    cZ
    @33
    cA
    wceq
    @34
    @1
    c1
    cle
    @33
    cA
    cabs
    fveq2
    breq1d
    lgslem2.z
    elrab2
    @35
    @6
    vx
    cB
    cz
    cZ
    @33
    cB
    wceq
    @34
    @5
    c1
    cle
    @33
    cB
    cabs
    fveq2
    breq1d
    lgslem2.z
    elrab2
    anbi12i
    @35
    @12
    vx
    @9
    cz
    cZ
    @33
    @9
    wceq
    @34
    @11
    c1
    cle
    @33
    @9
    cabs
    fveq2
    breq1d
    lgslem2.z
    elrab2
    3imtr4i
end
