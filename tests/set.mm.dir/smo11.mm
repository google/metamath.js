include "wf.mm"
include "wsmo.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "wf1.mm"
include "simpl.mm"
include "wfn.mm"
include "ffn.mm"
include "wcel.mm"
include "word.mm"
include "smodm2.mm"
include "ordelord.mm"
include "ex.mm"
include "syl.mm"
include "anim12d.mm"
include "wel.mm"
include "w3o.mm"
include "ordtri3or.mm"
include "w3a.mm"
include "simp1rr.mm"
include "smoel2.mm"
include "ralrimivva.mm"
include "adantr.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "simp3.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "raleqbi1dv.mm"
include "rspcv.mm"
include "eleq1d.mm"
include "rspccv.mm"
include "syl6.mm"
include "3imp.mm"
include "eleq1.mm"
include "biimpac.mm"
include "sylan.mm"
include "syl31anc.mm"
include "wn.mm"
include "con0.mm"
include "smofvon2.mm"
include "eloni.mm"
include "ordirr.mm"
include "3syl.mm"
include "ad2antlr.mm"
include "pm2.21dd.mm"
include "3exp.mm"
include "ax-1.mm"
include "a1i.mm"
include "simp1rl.mm"
include "eleq2.mm"
include "3jaod.mm"
include "syl5.mm"
include "mpdd.mm"
include "ralrimivv.mm"
include "dff13.mm"
include "sylanbrc.mm"

theorem smo11
  let cA: class A
  let cB: class B
  let cF: class F
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( F : A --> B /\ Smo F ) -> F : A -1-1-> B )

  proof
    cA
    cB
    cF
    wf
    #
    cF
    wsmo
    #
    wa
    @0
    vz
    cv
    #
    cF
    cfv
    #
    vw
    cv
    #
    cF
    cfv
    #
    wceq
    #
    vz
    vw
    weq
    #
    wi
    #
    vw
    cA
    wral
    vz
    cA
    wral
    #
    cA
    cB
    cF
    wf1
    @0
    @1
    simpl
    @0
    cF
    cA
    wfn
    #
    @1
    @9
    cA
    cB
    cF
    ffn
    @10
    @1
    wa
    #
    @8
    vz
    vw
    cA
    cA
    @11
    @2
    cA
    wcel
    #
    @4
    cA
    wcel
    #
    wa
    #
    @2
    word
    #
    @4
    word
    #
    wa
    #
    @8
    @11
    @12
    @15
    @13
    @16
    @11
    cA
    word
    #
    @12
    @15
    wi
    cA
    cF
    smodm2
    #
    @18
    @12
    @15
    cA
    @2
    ordelord
    ex
    syl
    @11
    @18
    @13
    @16
    wi
    @19
    @18
    @13
    @16
    cA
    @4
    ordelord
    ex
    syl
    anim12d
    @11
    @14
    @17
    @8
    wi
    @17
    vz
    vw
    wel
    #
    @7
    vw
    vz
    wel
    #
    w3o
    @11
    @14
    wa
    #
    @8
    @2
    @4
    ordtri3or
    @22
    @20
    @8
    @7
    @21
    @22
    @20
    @6
    @7
    @22
    @20
    @6
    w3a
    #
    @5
    @5
    wcel
    #
    @7
    @23
    @13
    vy
    cv
    #
    cF
    cfv
    #
    vx
    cv
    #
    cF
    cfv
    #
    wcel
    #
    vy
    @27
    wral
    #
    vx
    cA
    wral
    #
    @20
    @6
    @24
    @12
    @13
    @11
    @20
    @6
    simp1rr
    @22
    @20
    @31
    @6
    @11
    @31
    @14
    @11
    @29
    vx
    vy
    cA
    @27
    cA
    @27
    @25
    cF
    smoel2
    ralrimivva
    adantr
    #
    3ad2ant1
    @22
    @20
    @6
    simp2
    @22
    @20
    @6
    simp3
    @13
    @31
    @20
    w3a
    @3
    @5
    wcel
    #
    @6
    @24
    @13
    @31
    @20
    @33
    @13
    @31
    @26
    @5
    wcel
    #
    vy
    @4
    wral
    #
    @20
    @33
    wi
    @30
    @35
    vx
    @4
    cA
    @29
    @34
    vy
    @27
    @4
    vx
    vw
    weq
    @28
    @5
    @26
    @27
    @4
    cF
    fveq2
    eleq2d
    raleqbi1dv
    rspcv
    @34
    @33
    vy
    @2
    @4
    vy
    vz
    weq
    @26
    @3
    @5
    @25
    @2
    cF
    fveq2
    eleq1d
    rspccv
    syl6
    3imp
    @6
    @33
    @24
    @3
    @5
    @5
    eleq1
    biimpac
    sylan
    syl31anc
    @22
    @20
    @24
    wn
    #
    @6
    @1
    @36
    @10
    @14
    @1
    @5
    con0
    wcel
    @5
    word
    @36
    @4
    cF
    smofvon2
    @5
    eloni
    @5
    ordirr
    3syl
    ad2antlr
    #
    3ad2ant1
    pm2.21dd
    3exp
    @7
    @8
    wi
    @22
    @7
    @6
    ax-1
    a1i
    @22
    @21
    @6
    @7
    @22
    @21
    @6
    w3a
    #
    @24
    @7
    @38
    @12
    @31
    @21
    @6
    @24
    @12
    @13
    @11
    @21
    @6
    simp1rl
    @22
    @21
    @31
    @6
    @32
    3ad2ant1
    @22
    @21
    @6
    simp2
    @22
    @21
    @6
    simp3
    @12
    @31
    @21
    w3a
    @5
    @3
    wcel
    #
    @6
    @24
    @12
    @31
    @21
    @39
    @12
    @31
    @26
    @3
    wcel
    #
    vy
    @2
    wral
    #
    @21
    @39
    wi
    @30
    @41
    vx
    @2
    cA
    @29
    @40
    vy
    @27
    @2
    vx
    vz
    weq
    @28
    @3
    @26
    @27
    @2
    cF
    fveq2
    eleq2d
    raleqbi1dv
    rspcv
    @40
    @39
    vy
    @4
    @2
    vy
    vw
    weq
    @26
    @5
    @3
    @25
    @4
    cF
    fveq2
    eleq1d
    rspccv
    syl6
    3imp
    @6
    @39
    @24
    @3
    @5
    @5
    eleq2
    biimpac
    sylan
    syl31anc
    @22
    @21
    @36
    @6
    @37
    3ad2ant1
    pm2.21dd
    3exp
    3jaod
    syl5
    ex
    mpdd
    ralrimivv
    sylan
    vz
    vw
    cA
    cB
    cF
    dff13
    sylanbrc
end
