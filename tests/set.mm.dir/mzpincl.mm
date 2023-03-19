include "cvv.mm"
include "wcel.mm"
include "cmzp.mm"
include "cfv.mm"
include "cmzpcl.mm"
include "cint.mm"
include "mzpval.mm"
include "cz.mm"
include "cmap.mm"
include "co.mm"
include "wss.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "wral.mm"
include "cmpt.mm"
include "wa.mm"
include "caddc.mm"
include "cof.mm"
include "cmul.mm"
include "mzpclall.mm"
include "intss1.mm"
include "syl.mm"
include "simpr.mm"
include "simplr.mm"
include "mzpcl1.mm"
include "syl2anc.mm"
include "ralrimiva.mm"
include "ovex.mm"
include "snex.mm"
include "xpex.mm"
include "elint2.mm"
include "sylibr.mm"
include "mzpcl2.mm"
include "mptex.mm"
include "jca.mm"
include "wi.mm"
include "vex.mm"
include "mzpcl34.mm"
include "3expib.mm"
include "ralimia.mm"
include "r19.26.mm"
include "3imtr3i.mm"
include "syl2anb.mm"
include "anbi12i.mm"
include "a1i.mm"
include "ralrimivv.mm"
include "jca32.mm"
include "elmzpcl.mm"
include "mpbird.mm"
include "eqeltrd.mm"

theorem mzpincl
  let cV: class V
  let vv: setvar v
  let vf: setvar f
  let vg: setvar g
  let va: setvar a


  assert |- ( V e. _V -> ( mzPoly ` V ) e. ( mzPolyCld ` V ) )

  proof
    cV
    cvv
    wcel
    #
    cV
    cmzp
    cfv
    cV
    cmzpcl
    cfv
    #
    cint
    #
    @1
    cV
    mzpval
    @0
    @2
    @1
    wcel
    @2
    cz
    cz
    cV
    cmap
    co
    #
    cmap
    co
    #
    wss
    #
    @3
    vf
    cv
    #
    csn
    #
    cxp
    #
    @2
    wcel
    #
    vf
    cz
    wral
    #
    vg
    @3
    @6
    vg
    cv
    #
    cfv
    #
    cmpt
    #
    @2
    wcel
    #
    vf
    cV
    wral
    #
    wa
    #
    @6
    @11
    caddc
    cof
    #
    co
    #
    @2
    wcel
    #
    @6
    @11
    cmul
    cof
    #
    co
    #
    @2
    wcel
    #
    wa
    #
    vg
    @2
    wral
    vf
    @2
    wral
    #
    wa
    wa
    @0
    @5
    @16
    @24
    @0
    @4
    @1
    wcel
    @5
    cV
    mzpclall
    @4
    @1
    intss1
    syl
    @0
    @10
    @15
    @0
    @9
    vf
    cz
    @0
    @6
    cz
    wcel
    #
    wa
    #
    @8
    va
    cv
    #
    wcel
    #
    va
    @1
    wral
    @9
    @26
    @28
    va
    @1
    @26
    @27
    @1
    wcel
    #
    wa
    @29
    @25
    @28
    @26
    @29
    simpr
    @0
    @25
    @29
    simplr
    @27
    @6
    cV
    mzpcl1
    syl2anc
    ralrimiva
    va
    @8
    @1
    @3
    @7
    cz
    cV
    cmap
    ovex
    #
    @6
    snex
    xpex
    elint2
    sylibr
    ralrimiva
    @0
    @14
    vf
    cV
    @0
    @6
    cV
    wcel
    #
    wa
    #
    @13
    @27
    wcel
    #
    va
    @1
    wral
    @14
    @32
    @33
    va
    @1
    @32
    @29
    wa
    @29
    @31
    @33
    @32
    @29
    simpr
    @0
    @31
    @29
    simplr
    @27
    vg
    @6
    cV
    mzpcl2
    syl2anc
    ralrimiva
    va
    @13
    @1
    vg
    @3
    @12
    @30
    mptex
    elint2
    sylibr
    ralrimiva
    jca
    @0
    @23
    vf
    vg
    @2
    @2
    @6
    @2
    wcel
    #
    @11
    @2
    wcel
    #
    wa
    #
    @23
    wi
    @0
    @36
    @18
    @27
    wcel
    #
    va
    @1
    wral
    #
    @21
    @27
    wcel
    #
    va
    @1
    wral
    #
    wa
    #
    @23
    @34
    @6
    @27
    wcel
    #
    va
    @1
    wral
    #
    @11
    @27
    wcel
    #
    va
    @1
    wral
    #
    @41
    @35
    va
    @6
    @1
    vf
    vex
    elint2
    va
    @11
    @1
    vg
    vex
    elint2
    @42
    @44
    wa
    #
    va
    @1
    wral
    @37
    @39
    wa
    #
    va
    @1
    wral
    @43
    @45
    wa
    @41
    @46
    @47
    va
    @1
    @29
    @42
    @44
    @47
    @27
    @6
    @11
    cV
    mzpcl34
    3expib
    ralimia
    @42
    @44
    va
    @1
    r19.26
    @37
    @39
    va
    @1
    r19.26
    3imtr3i
    syl2anb
    @19
    @38
    @22
    @40
    va
    @18
    @1
    @6
    @11
    @17
    ovex
    elint2
    va
    @21
    @1
    @6
    @11
    @20
    ovex
    elint2
    anbi12i
    sylibr
    a1i
    ralrimivv
    jca32
    vg
    @2
    vf
    vg
    vf
    vf
    cV
    elmzpcl
    mpbird
    eqeltrd
end
