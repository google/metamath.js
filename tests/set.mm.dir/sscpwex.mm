include "cv.mm"
include "cssc.mm"
include "wbr.mm"
include "cab.mm"
include "crn.mm"
include "cuni.mm"
include "cpw.mm"
include "cdm.mm"
include "cpm.mm"
include "co.mm"
include "ovex.mm"
include "cxp.mm"
include "wfn.mm"
include "cfv.mm"
include "cixp.mm"
include "wcel.mm"
include "wrex.mm"
include "wa.mm"
include "wex.mm"
include "brssc.mm"
include "cvv.mm"
include "wf.mm"
include "wss.mm"
include "simpl.mm"
include "vex.mm"
include "xpex.mm"
include "fnex.mm"
include "sylancl.mm"
include "rnexg.mm"
include "uniexg.mm"
include "pwexg.mm"
include "4syl.mm"
include "wceq.mm"
include "fndm.mm"
include "adantr.mm"
include "syl6eqel.mm"
include "ss2ixp.mm"
include "fvssunirn.mm"
include "sspwb.mm"
include "mpbi.mm"
include "a1i.mm"
include "mprg.mm"
include "simprr.mm"
include "sseldi.mm"
include "elixpconst.mm"
include "sylib.mm"
include "elpwi.mm"
include "ad2antrl.mm"
include "xpss12.mm"
include "syl2anc.mm"
include "sseqtr4d.mm"
include "elpm2r.mm"
include "syl22anc.mm"
include "rexlimdvaa.mm"
include "imp.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "abssi.mm"
include "ssexi.mm"

theorem sscpwex
  let vh: setvar h
  let cJ: class J
  let vc: setvar c
  let vf: setvar f
  let vg: setvar g
  let vj: setvar j
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cH: class H

  disjoint J h
  disjoint c f
  disjoint c g
  disjoint c h
  disjoint c j
  disjoint c s
  disjoint c t
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint f g
  disjoint f h
  disjoint f j
  disjoint f s
  disjoint f t
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint g h
  disjoint g j
  disjoint g s
  disjoint g t
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint h j
  disjoint h s
  disjoint h t
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint j s
  disjoint j t
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint s t
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint H h
  disjoint H j
  disjoint H s
  disjoint H t
  disjoint H x
  disjoint J j
  disjoint J s
  disjoint J t
  disjoint J x
  assert |- { h | h C_cat J } e. _V

  proof
    vh
    cv
    #
    cJ
    cssc
    wbr
    #
    vh
    cab
    cJ
    crn
    #
    cuni
    #
    cpw
    #
    cJ
    cdm
    #
    cpm
    co
    #
    @4
    @5
    cpm
    ovex
    @1
    vh
    @6
    @1
    cJ
    vt
    cv
    #
    @7
    cxp
    #
    wfn
    #
    @0
    vx
    vs
    cv
    #
    @10
    cxp
    #
    vx
    cv
    #
    cJ
    cfv
    #
    cpw
    #
    cixp
    #
    wcel
    #
    vs
    @7
    cpw
    #
    wrex
    #
    wa
    #
    vt
    wex
    @0
    @6
    wcel
    #
    vx
    vt
    @0
    cJ
    vs
    brssc
    @19
    @20
    vt
    @9
    @18
    @20
    @9
    @16
    @20
    vs
    @17
    @9
    @10
    @17
    wcel
    #
    @16
    wa
    #
    wa
    #
    @4
    cvv
    wcel
    #
    @5
    cvv
    wcel
    @11
    @4
    @0
    wf
    #
    @11
    @5
    wss
    @20
    @23
    cJ
    cvv
    wcel
    #
    @2
    cvv
    wcel
    @3
    cvv
    wcel
    @24
    @23
    @9
    @8
    cvv
    wcel
    @26
    @9
    @22
    simpl
    @7
    @7
    vt
    vex
    #
    @27
    xpex
    #
    @8
    cvv
    cJ
    fnex
    sylancl
    cJ
    cvv
    rnexg
    @2
    cvv
    uniexg
    @3
    cvv
    pwexg
    4syl
    @23
    @5
    @8
    cvv
    @9
    @5
    @8
    wceq
    @22
    @8
    cJ
    fndm
    adantr
    #
    @28
    syl6eqel
    @23
    @0
    vx
    @11
    @4
    cixp
    #
    wcel
    @25
    @23
    @15
    @30
    @0
    @14
    @4
    wss
    #
    @15
    @30
    wss
    vx
    @11
    vx
    @11
    @14
    @4
    ss2ixp
    @31
    @12
    @11
    wcel
    @13
    @3
    wss
    @31
    cJ
    @12
    fvssunirn
    @13
    @3
    sspwb
    mpbi
    a1i
    mprg
    @9
    @21
    @16
    simprr
    sseldi
    vx
    @11
    @4
    @0
    vh
    vex
    elixpconst
    sylib
    @23
    @11
    @8
    @5
    @23
    @10
    @7
    wss
    #
    @32
    @11
    @8
    wss
    @21
    @32
    @9
    @16
    @10
    @7
    elpwi
    ad2antrl
    #
    @33
    @10
    @7
    @10
    @7
    xpss12
    syl2anc
    @29
    sseqtr4d
    @4
    @5
    @11
    @0
    cvv
    cvv
    elpm2r
    syl22anc
    rexlimdvaa
    imp
    exlimiv
    sylbi
    abssi
    ssexi
end
