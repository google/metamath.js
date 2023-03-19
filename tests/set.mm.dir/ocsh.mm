include "chil.mm"
include "wss.mm"
include "cort.mm"
include "cfv.mm"
include "c0v.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cva.mm"
include "co.mm"
include "wral.mm"
include "csm.mm"
include "cc.mm"
include "csh.mm"
include "csp.mm"
include "cc0.mm"
include "wceq.mm"
include "crab.mm"
include "ocval.mm"
include "ssrab2.mm"
include "syl6eqss.mm"
include "ssel.mm"
include "hi01.mm"
include "syl6.mm"
include "ralrimiv.mm"
include "ax-hv0cl.mm"
include "jctil.mm"
include "ocel.mm"
include "mpbird.mm"
include "jca.mm"
include "wi.mm"
include "ssel2.mm"
include "caddc.mm"
include "ax-his2.mm"
include "3expa.mm"
include "oveq12.mm"
include "00id.mm"
include "syl6eq.mm"
include "sylan9eq.mm"
include "ex.mm"
include "ancoms.mm"
include "sylan.mm"
include "an32s.mm"
include "ralimdva.mm"
include "imdistanda.mm"
include "hvaddcl.mm"
include "anim1i.mm"
include "anbi12d.mm"
include "an4.mm"
include "r19.26.mm"
include "anbi2i.mm"
include "bitr4i.mm"
include "syl6bb.mm"
include "3imtr4d.mm"
include "ralrimivv.mm"
include "cmul.mm"
include "mul01.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "syl5ibrcom.mm"
include "ad2antrl.mm"
include "wb.mm"
include "w3a.mm"
include "ax-his3.mm"
include "sylibrd.mm"
include "hvmulcl.mm"
include "anbi2d.mm"
include "anass.mm"
include "syl6bbr.mm"
include "issh2.mm"
include "sylanbrc.mm"

theorem ocsh
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cH: class H
  let cB: class B


  assert |- ( A C_ ~H -> ( _|_ ` A ) e. SH )

  proof
    cA
    chil
    wss
    #
    cA
    cort
    cfv
    #
    chil
    wss
    #
    c0v
    @1
    wcel
    #
    wa
    vx
    cv
    #
    vy
    cv
    #
    cva
    co
    #
    @1
    wcel
    #
    vy
    @1
    wral
    vx
    @1
    wral
    #
    @4
    @5
    csm
    co
    #
    @1
    wcel
    #
    vy
    @1
    wral
    vx
    cc
    wral
    #
    wa
    @1
    csh
    wcel
    @0
    @2
    @3
    @0
    @1
    @4
    @5
    csp
    co
    cc0
    wceq
    vy
    cA
    wral
    #
    vx
    chil
    crab
    chil
    vx
    vy
    cA
    ocval
    @12
    vx
    chil
    ssrab2
    syl6eqss
    @0
    @3
    c0v
    chil
    wcel
    #
    c0v
    @5
    csp
    co
    cc0
    wceq
    #
    vy
    cA
    wral
    #
    wa
    @0
    @15
    @13
    @0
    @14
    vy
    cA
    @0
    @5
    cA
    wcel
    @5
    chil
    wcel
    #
    @14
    cA
    chil
    @5
    ssel
    @5
    hi01
    syl6
    ralrimiv
    ax-hv0cl
    jctil
    vy
    c0v
    cA
    ocel
    mpbird
    jca
    @0
    @8
    @11
    @0
    @7
    vx
    vy
    @1
    @1
    @0
    @4
    chil
    wcel
    #
    @16
    wa
    #
    @4
    vz
    cv
    #
    csp
    co
    #
    cc0
    wceq
    #
    @5
    @19
    csp
    co
    #
    cc0
    wceq
    #
    wa
    #
    vz
    cA
    wral
    #
    wa
    #
    @6
    chil
    wcel
    #
    @6
    @19
    csp
    co
    #
    cc0
    wceq
    #
    vz
    cA
    wral
    #
    wa
    #
    @4
    @1
    wcel
    #
    @5
    @1
    wcel
    #
    wa
    #
    @7
    @0
    @26
    @18
    @30
    wa
    @31
    @0
    @18
    @25
    @30
    @0
    @18
    wa
    @24
    @29
    vz
    cA
    @0
    @19
    cA
    wcel
    #
    @18
    @24
    @29
    wi
    #
    @0
    @35
    wa
    #
    @19
    chil
    wcel
    #
    @18
    @36
    cA
    chil
    @19
    ssel2
    #
    @18
    @38
    @36
    @18
    @38
    wa
    #
    @24
    @29
    @40
    @24
    @28
    @20
    @22
    caddc
    co
    #
    cc0
    @17
    @16
    @38
    @28
    @41
    wceq
    @4
    @5
    @19
    ax-his2
    3expa
    @24
    @41
    cc0
    cc0
    caddc
    co
    cc0
    @20
    cc0
    @22
    cc0
    caddc
    oveq12
    00id
    syl6eq
    sylan9eq
    ex
    ancoms
    sylan
    an32s
    ralimdva
    imdistanda
    @18
    @27
    @30
    @4
    @5
    hvaddcl
    anim1i
    syl6
    @0
    @34
    @17
    @21
    vz
    cA
    wral
    #
    wa
    #
    @16
    @23
    vz
    cA
    wral
    #
    wa
    #
    wa
    #
    @26
    @0
    @32
    @43
    @33
    @45
    vz
    @4
    cA
    ocel
    vz
    @5
    cA
    ocel
    #
    anbi12d
    @46
    @18
    @42
    @44
    wa
    #
    wa
    @26
    @17
    @42
    @16
    @44
    an4
    @25
    @48
    @18
    @21
    @23
    vz
    cA
    r19.26
    anbi2i
    bitr4i
    syl6bb
    vz
    @6
    cA
    ocel
    3imtr4d
    ralrimivv
    @0
    @10
    vx
    vy
    cc
    @1
    @0
    @4
    cc
    wcel
    #
    @16
    wa
    #
    @44
    wa
    #
    @9
    chil
    wcel
    #
    @9
    @19
    csp
    co
    #
    cc0
    wceq
    #
    vz
    cA
    wral
    #
    wa
    #
    @49
    @33
    wa
    #
    @10
    @0
    @51
    @50
    @55
    wa
    @56
    @0
    @50
    @44
    @55
    @0
    @50
    wa
    @23
    @54
    vz
    cA
    @0
    @35
    @50
    @23
    @54
    wi
    #
    @37
    @38
    @50
    @58
    @39
    @38
    @50
    wa
    @23
    @4
    @22
    cmul
    co
    #
    cc0
    wceq
    #
    @54
    @49
    @23
    @60
    wi
    @38
    @16
    @49
    @60
    @23
    @4
    cc0
    cmul
    co
    #
    cc0
    wceq
    @4
    mul01
    @23
    @59
    @61
    cc0
    @22
    cc0
    @4
    cmul
    oveq2
    eqeq1d
    syl5ibrcom
    ad2antrl
    @50
    @38
    @54
    @60
    wb
    #
    @49
    @16
    @38
    @62
    @49
    @16
    @38
    w3a
    @53
    @59
    cc0
    @4
    @5
    @19
    ax-his3
    eqeq1d
    3expa
    ancoms
    sylibrd
    sylan
    an32s
    ralimdva
    imdistanda
    @50
    @52
    @55
    @4
    @5
    hvmulcl
    anim1i
    syl6
    @0
    @57
    @49
    @45
    wa
    @51
    @0
    @33
    @45
    @49
    @47
    anbi2d
    @49
    @16
    @44
    anass
    syl6bbr
    vz
    @9
    cA
    ocel
    3imtr4d
    ralrimivv
    jca
    vx
    vy
    @1
    issh2
    sylanbrc
end
