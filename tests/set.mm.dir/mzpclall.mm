include "cz.mm"
include "cv.mm"
include "cmap.mm"
include "co.mm"
include "cmzpcl.mm"
include "cfv.mm"
include "wcel.mm"
include "cvv.mm"
include "wceq.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "fveq2.mm"
include "eleq12d.mm"
include "wss.mm"
include "csn.mm"
include "cxp.mm"
include "wral.mm"
include "cmpt.mm"
include "wa.mm"
include "caddc.mm"
include "cof.mm"
include "cmul.mm"
include "ssid.mm"
include "ovex.mm"
include "zex.mm"
include "constmap.mm"
include "rgen.mm"
include "wf.mm"
include "vex.mm"
include "elmap.mm"
include "ffvelrn.mm"
include "sylanb.mm"
include "ancoms.mm"
include "eqid.mm"
include "fmptd.mm"
include "sylibr.mm"
include "pm3.2i.mm"
include "zaddcl.mm"
include "adantl.mm"
include "simpl.mm"
include "simpr.mm"
include "ovexd.mm"
include "inidm.mm"
include "off.mm"
include "zmulcl.mm"
include "jca.mm"
include "anbi12i.mm"
include "3imtr4i.mm"
include "rgen2a.mm"
include "wb.mm"
include "elmzpcl.mm"
include "ax-mp.mm"
include "mpbir2an.mm"
include "vtoclg.mm"

theorem mzpclall
  let cV: class V
  let vv: setvar v
  let vf: setvar f
  let vg: setvar g
  let va: setvar a
  let vb: setvar b
  let cP: class P
  let cF: class F
  let cG: class G


  assert |- ( V e. _V -> ( ZZ ^m ( ZZ ^m V ) ) e. ( mzPolyCld ` V ) )

  proof
    cz
    cz
    vv
    cv
    #
    cmap
    co
    #
    cmap
    co
    #
    @0
    cmzpcl
    cfv
    #
    wcel
    #
    cz
    cz
    cV
    cmap
    co
    #
    cmap
    co
    #
    cV
    cmzpcl
    cfv
    #
    wcel
    vv
    cV
    cvv
    @0
    cV
    wceq
    #
    @2
    @6
    @3
    @7
    @8
    @1
    @5
    cz
    cmap
    @0
    cV
    cz
    cmap
    oveq2
    oveq2d
    @0
    cV
    cmzpcl
    fveq2
    eleq12d
    @4
    @2
    @2
    wss
    #
    @1
    vf
    cv
    #
    csn
    cxp
    @2
    wcel
    #
    vf
    cz
    wral
    #
    vg
    @1
    @10
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
    @0
    wral
    #
    wa
    #
    @10
    @13
    caddc
    cof
    co
    #
    @2
    wcel
    #
    @10
    @13
    cmul
    cof
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
    #
    @2
    ssid
    @18
    @24
    @12
    @17
    @11
    vf
    cz
    @1
    @10
    cz
    cz
    @0
    cmap
    ovex
    #
    zex
    constmap
    rgen
    @16
    vf
    @0
    @10
    @0
    wcel
    #
    @1
    cz
    @15
    wf
    @16
    @27
    vg
    @1
    @14
    cz
    @15
    @13
    @1
    wcel
    #
    @27
    @14
    cz
    wcel
    #
    @28
    @0
    cz
    @13
    wf
    @27
    @29
    cz
    @0
    @13
    zex
    vv
    vex
    #
    elmap
    @0
    cz
    @10
    @13
    ffvelrn
    sylanb
    ancoms
    @15
    eqid
    fmptd
    cz
    @1
    @15
    zex
    @26
    elmap
    sylibr
    rgen
    pm3.2i
    @23
    vf
    vg
    @2
    @1
    cz
    @10
    wf
    #
    @1
    cz
    @13
    wf
    #
    wa
    #
    @1
    cz
    @19
    wf
    #
    @1
    cz
    @21
    wf
    #
    wa
    @10
    @2
    wcel
    #
    @13
    @2
    wcel
    #
    wa
    @23
    @33
    @34
    @35
    @33
    va
    vb
    @1
    @1
    @1
    caddc
    cz
    cz
    cz
    @10
    @13
    cvv
    cvv
    va
    cv
    #
    cz
    wcel
    vb
    cv
    #
    cz
    wcel
    wa
    #
    @38
    @39
    caddc
    co
    cz
    wcel
    @33
    @38
    @39
    zaddcl
    adantl
    @31
    @32
    simpl
    #
    @31
    @32
    simpr
    #
    @33
    cz
    @0
    cmap
    ovexd
    #
    @43
    @1
    inidm
    #
    off
    @33
    va
    vb
    @1
    @1
    @1
    cmul
    cz
    cz
    cz
    @10
    @13
    cvv
    cvv
    @40
    @38
    @39
    cmul
    co
    cz
    wcel
    @33
    @38
    @39
    zmulcl
    adantl
    @41
    @42
    @43
    @43
    @44
    off
    jca
    @36
    @31
    @37
    @32
    cz
    @1
    @10
    zex
    @26
    elmap
    cz
    @1
    @13
    zex
    @26
    elmap
    anbi12i
    @20
    @34
    @22
    @35
    cz
    @1
    @19
    zex
    @26
    elmap
    cz
    @1
    @21
    zex
    @26
    elmap
    anbi12i
    3imtr4i
    rgen2a
    pm3.2i
    @0
    cvv
    wcel
    @4
    @9
    @25
    wa
    wb
    @30
    vg
    @2
    vf
    vg
    vf
    vf
    @0
    elmzpcl
    ax-mp
    mpbir2an
    vtoclg
end
