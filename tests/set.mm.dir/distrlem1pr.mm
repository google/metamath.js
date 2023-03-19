include "cnp.mm"
include "wcel.mm"
include "w3a.mm"
include "cpp.mm"
include "co.mm"
include "cmp.mm"
include "cv.mm"
include "cmq.mm"
include "wceq.mm"
include "wrex.mm"
include "wb.mm"
include "wa.mm"
include "addclpr.mm"
include "df-mp.mm"
include "mulclnq.mm"
include "genpelv.mm"
include "sylan2.mm"
include "3impb.mm"
include "wi.mm"
include "cplq.mm"
include "df-plp.mm"
include "addclnq.mm"
include "3adant1.mm"
include "adantr.mm"
include "simprr.mm"
include "simpr.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "biimpac.mm"
include "distrnq.mm"
include "syl6eq.mm"
include "syl2an.mm"
include "mulclpr.mm"
include "3adant3.mm"
include "ad2antrr.mm"
include "3adant2.mm"
include "simpll.mm"
include "genpprecl.mm"
include "impl.mm"
include "adantlrr.mm"
include "simplr.mm"
include "imp.mm"
include "syl22anc.mm"
include "eqeltrd.mm"
include "exp32.mm"
include "rexlimdvv.mm"
include "sylbid.mm"
include "com34.mm"
include "impd.mm"
include "ssrdv.mm"

theorem distrlem1pr
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h


  assert |- ( ( A e. P. /\ B e. P. /\ C e. P. ) -> ( A .P. ( B +P. C ) ) C_ ( ( A .P. B ) +P. ( A .P. C ) ) )

  proof
    cA
    cnp
    wcel
    #
    cB
    cnp
    wcel
    #
    cC
    cnp
    wcel
    #
    w3a
    #
    vw
    cA
    cB
    cC
    cpp
    co
    #
    cmp
    co
    #
    cA
    cB
    cmp
    co
    #
    cA
    cC
    cmp
    co
    #
    cpp
    co
    #
    @3
    vw
    cv
    #
    @5
    wcel
    #
    @9
    vx
    cv
    #
    vv
    cv
    #
    cmq
    co
    #
    wceq
    #
    vv
    @4
    wrex
    vx
    cA
    wrex
    #
    @9
    @8
    wcel
    #
    @0
    @1
    @2
    @10
    @15
    wb
    #
    @1
    @2
    wa
    @0
    @4
    cnp
    wcel
    @17
    cB
    cC
    addclpr
    vf
    vg
    vh
    vy
    vz
    cA
    @4
    @9
    vx
    vv
    cmp
    cmq
    vy
    vz
    vf
    vg
    vh
    df-mp
    #
    vg
    cv
    #
    vh
    cv
    #
    mulclnq
    #
    genpelv
    sylan2
    3impb
    @3
    @14
    @16
    vx
    vv
    cA
    @4
    @3
    @11
    cA
    wcel
    #
    @12
    @4
    wcel
    #
    @14
    @16
    wi
    @3
    @22
    @14
    @23
    @16
    @3
    @22
    @14
    @23
    @16
    wi
    @3
    @22
    @14
    wa
    #
    wa
    #
    @23
    @12
    vy
    cv
    #
    vz
    cv
    #
    cplq
    co
    #
    wceq
    #
    vz
    cC
    wrex
    vy
    cB
    wrex
    #
    @16
    @3
    @23
    @30
    wb
    #
    @24
    @1
    @2
    @31
    @0
    vf
    vg
    vh
    vw
    vx
    cB
    cC
    @12
    vy
    vz
    cpp
    cplq
    vw
    vx
    vf
    vg
    vh
    df-plp
    #
    @19
    @20
    addclnq
    #
    genpelv
    3adant1
    adantr
    @25
    @29
    @16
    vy
    vz
    cB
    cC
    @25
    @26
    cB
    wcel
    #
    @27
    cC
    wcel
    #
    wa
    #
    @29
    @16
    @25
    @36
    @29
    wa
    #
    wa
    #
    @9
    @11
    @26
    cmq
    co
    #
    @11
    @27
    cmq
    co
    #
    cplq
    co
    #
    @8
    @25
    @14
    @29
    @9
    @41
    wceq
    @37
    @3
    @22
    @14
    simprr
    @36
    @29
    simpr
    @14
    @29
    wa
    @9
    @11
    @28
    cmq
    co
    #
    @41
    @29
    @14
    @9
    @42
    wceq
    @29
    @13
    @42
    @9
    @12
    @28
    @11
    cmq
    oveq2
    eqeq2d
    biimpac
    @11
    @26
    @27
    distrnq
    syl6eq
    syl2an
    @38
    @6
    cnp
    wcel
    #
    @7
    cnp
    wcel
    #
    @39
    @6
    wcel
    #
    @40
    @7
    wcel
    #
    @41
    @8
    wcel
    #
    @3
    @43
    @24
    @37
    @0
    @1
    @43
    @2
    cA
    cB
    mulclpr
    3adant3
    ad2antrr
    @3
    @44
    @24
    @37
    @0
    @2
    @44
    @1
    cA
    cC
    mulclpr
    3adant2
    ad2antrr
    @37
    @25
    @34
    @45
    @34
    @35
    @29
    simpll
    @3
    @22
    @34
    @45
    @14
    @3
    @22
    @34
    @45
    @0
    @1
    @22
    @34
    wa
    @45
    wi
    @2
    vf
    vg
    vh
    vy
    vz
    cA
    cB
    @11
    @26
    cmp
    cmq
    @18
    @21
    genpprecl
    3adant3
    impl
    adantlrr
    sylan2
    @37
    @25
    @35
    @46
    @34
    @35
    @29
    simplr
    @3
    @22
    @35
    @46
    @14
    @3
    @22
    @35
    @46
    @0
    @2
    @22
    @35
    wa
    @46
    wi
    @1
    vf
    vg
    vh
    vy
    vz
    cA
    cC
    @11
    @27
    cmp
    cmq
    @18
    @21
    genpprecl
    3adant2
    impl
    adantlrr
    sylan2
    @43
    @44
    wa
    @45
    @46
    wa
    @47
    vf
    vg
    vh
    vw
    vx
    @6
    @7
    @39
    @40
    cpp
    cplq
    @32
    @33
    genpprecl
    imp
    syl22anc
    eqeltrd
    exp32
    rexlimdvv
    sylbid
    exp32
    com34
    impd
    rexlimdvv
    sylbid
    ssrdv
end
