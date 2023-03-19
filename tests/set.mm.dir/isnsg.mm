include "cnsg.mm"
include "cfv.mm"
include "wcel.mm"
include "cgrp.mm"
include "csubg.mm"
include "cv.mm"
include "co.mm"
include "wb.mm"
include "wral.mm"
include "wa.mm"
include "cdm.mm"
include "cplusg.mm"
include "wsbc.mm"
include "cbs.mm"
include "crab.mm"
include "df-nsg.mm"
include "dmmptss.mm"
include "elfvdm.mm"
include "sseldi.mm"
include "subgrcl.mm"
include "adantr.mm"
include "wceq.mm"
include "fveq2.mm"
include "cvv.mm"
include "fvexd.mm"
include "syl6eqr.mm"
include "simpl.mm"
include "fveq2d.mm"
include "simplr.mm"
include "simpr.mm"
include "oveqd.mm"
include "eleq1d.mm"
include "bibi12d.mm"
include "raleqbidv.mm"
include "sbcied2.mm"
include "rabeqbidv.mm"
include "fvex.mm"
include "rabex.mm"
include "fvmpt.mm"
include "eleq2d.mm"
include "eleq2.mm"
include "2ralbidv.mm"
include "elrab.mm"
include "syl6bb.mm"
include "pm5.21nii.mm"

theorem isnsg
  let vx: setvar x
  let vy: setvar y
  let c.pl: class .+
  let cS: class S
  let cG: class G
  let cX: class X
  let cA: class A
  let vb: setvar b
  let vg: setvar g
  let vp: setvar p
  let vs: setvar s
  let vz: setvar z
  let cB: class B
  assume isnsg.1: |- X = ( Base ` G )
  assume isnsg.2: |- .+ = ( +g ` G )

  disjoint x y
  disjoint G x
  disjoint G y
  disjoint .+ x
  disjoint .+ y
  disjoint S x
  disjoint S y
  disjoint X x
  disjoint X y
  disjoint A x
  disjoint A y
  disjoint b g
  disjoint b p
  disjoint b s
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint G b
  disjoint g p
  disjoint g s
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint G g
  disjoint p s
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint G p
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint G s
  disjoint x z
  disjoint y z
  disjoint G z
  disjoint .+ b
  disjoint .+ g
  disjoint .+ p
  disjoint .+ s
  disjoint .+ z
  disjoint S s
  disjoint S z
  disjoint B y
  disjoint X b
  disjoint X g
  disjoint X p
  disjoint X s
  disjoint X z
  assert |- ( S e. ( NrmSGrp ` G ) <-> ( S e. ( SubGrp ` G ) /\ A. x e. X A. y e. X ( ( x .+ y ) e. S <-> ( y .+ x ) e. S ) ) )

  proof
    cS
    cG
    cnsg
    cfv
    #
    wcel
    #
    cG
    cgrp
    wcel
    #
    cS
    cG
    csubg
    cfv
    #
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    c.pl
    co
    #
    cS
    wcel
    #
    @6
    @5
    c.pl
    co
    #
    cS
    wcel
    #
    wb
    #
    vy
    cX
    wral
    vx
    cX
    wral
    #
    wa
    #
    @1
    cnsg
    cdm
    cgrp
    cG
    vg
    cgrp
    @5
    @6
    vp
    cv
    #
    co
    #
    vs
    cv
    #
    wcel
    #
    @6
    @5
    @14
    co
    #
    @16
    wcel
    #
    wb
    #
    vy
    vb
    cv
    #
    wral
    #
    vx
    @21
    wral
    #
    vp
    vg
    cv
    #
    cplusg
    cfv
    #
    wsbc
    #
    vb
    @24
    cbs
    cfv
    #
    wsbc
    #
    vs
    @24
    csubg
    cfv
    #
    crab
    #
    cnsg
    vx
    vy
    vg
    vs
    vp
    vb
    df-nsg
    #
    dmmptss
    cS
    cG
    cnsg
    elfvdm
    sseldi
    @4
    @2
    @12
    cS
    cG
    subgrcl
    adantr
    @2
    @1
    cS
    @7
    @16
    wcel
    #
    @9
    @16
    wcel
    #
    wb
    #
    vy
    cX
    wral
    #
    vx
    cX
    wral
    #
    vs
    @3
    crab
    #
    wcel
    @13
    @2
    @0
    @37
    cS
    vg
    cG
    @30
    @37
    cgrp
    cnsg
    @24
    cG
    wceq
    #
    @28
    @36
    vs
    @29
    @3
    @24
    cG
    csubg
    fveq2
    @38
    @26
    @36
    vb
    @27
    cX
    cvv
    @38
    @24
    cbs
    fvexd
    @38
    @27
    cG
    cbs
    cfv
    cX
    @24
    cG
    cbs
    fveq2
    isnsg.1
    syl6eqr
    @38
    @21
    cX
    wceq
    #
    wa
    #
    @23
    @36
    vp
    @25
    c.pl
    cvv
    @40
    @24
    cplusg
    fvexd
    @40
    @25
    cG
    cplusg
    cfv
    c.pl
    @40
    @24
    cG
    cplusg
    @38
    @39
    simpl
    fveq2d
    isnsg.2
    syl6eqr
    @40
    @14
    c.pl
    wceq
    #
    wa
    #
    @22
    @35
    vx
    @21
    cX
    @38
    @39
    @41
    simplr
    #
    @42
    @20
    @34
    vy
    @21
    cX
    @43
    @42
    @17
    @32
    @19
    @33
    @42
    @15
    @7
    @16
    @42
    @14
    c.pl
    @5
    @6
    @40
    @41
    simpr
    #
    oveqd
    eleq1d
    @42
    @18
    @9
    @16
    @42
    @14
    c.pl
    @6
    @5
    @44
    oveqd
    eleq1d
    bibi12d
    raleqbidv
    raleqbidv
    sbcied2
    sbcied2
    rabeqbidv
    @31
    @36
    vs
    @3
    cG
    csubg
    fvex
    rabex
    fvmpt
    eleq2d
    @36
    @12
    vs
    cS
    @3
    @16
    cS
    wceq
    #
    @34
    @11
    vx
    vy
    cX
    cX
    @45
    @32
    @8
    @33
    @10
    @16
    cS
    @7
    eleq2
    @16
    cS
    @9
    eleq2
    bibi12d
    2ralbidv
    elrab
    syl6bb
    pm5.21nii
end
