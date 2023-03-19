include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "co.mm"
include "wne.mm"
include "wral.mm"
include "wa.mm"
include "cir.mm"
include "cdm.mm"
include "cfv.mm"
include "elfvdm.mm"
include "eleq2s.mm"
include "elex.mm"
include "syl.mm"
include "cbs.mm"
include "cdif.mm"
include "eldifi.mm"
include "syl6eleq.mm"
include "elfvexd.mm"
include "adantr.mm"
include "crab.mm"
include "cui.mm"
include "cmulr.mm"
include "csb.mm"
include "wceq.mm"
include "fvex.mm"
include "difexg.mm"
include "mp1i.mm"
include "simpr.mm"
include "simpl.mm"
include "fveq2d.mm"
include "syl6eqr.mm"
include "difeq12d.mm"
include "eqtrd.mm"
include "oveqd.mm"
include "neeq1d.mm"
include "raleqbidv.mm"
include "rabeqbidv.mm"
include "csbied.mm"
include "df-irred.mm"
include "eqeltri.mm"
include "ax-mp.mm"
include "rabex.mm"
include "fvmpt.mm"
include "syl5eq.mm"
include "eleq2d.mm"
include "neeq2.mm"
include "2ralbidv.mm"
include "elrab.mm"
include "syl6bb.mm"
include "pm5.21nii.mm"

theorem isirred
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let cU: class U
  let cI: class I
  let cN: class N
  let cX: class X
  let vb: setvar b
  let vr: setvar r
  let vz: setvar z
  assume irred.1: |- B = ( Base ` R )
  assume irred.2: |- U = ( Unit ` R )
  assume irred.3: |- I = ( Irred ` R )
  assume irred.4: |- N = ( B \ U )
  assume irred.5: |- .x. = ( .r ` R )

  disjoint x y
  disjoint N x
  disjoint N y
  disjoint R x
  disjoint R y
  disjoint X x
  disjoint X y
  disjoint b r
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint N b
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint N r
  disjoint x z
  disjoint y z
  disjoint N z
  disjoint R b
  disjoint R r
  disjoint R z
  disjoint .x. b
  disjoint .x. r
  disjoint .x. z
  disjoint X z
  assert |- ( X e. I <-> ( X e. N /\ A. x e. N A. y e. N ( x .x. y ) =/= X ) )

  proof
    cX
    cI
    wcel
    #
    cR
    cvv
    wcel
    #
    cX
    cN
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    c.x
    co
    #
    cX
    wne
    #
    vy
    cN
    wral
    vx
    cN
    wral
    #
    wa
    #
    @0
    cR
    cir
    cdm
    #
    wcel
    #
    @1
    @10
    cX
    cR
    cir
    cfv
    #
    cI
    cX
    cR
    cir
    elfvdm
    irred.3
    eleq2s
    cR
    @9
    elex
    syl
    @2
    @1
    @7
    @2
    cX
    cbs
    cR
    @2
    cX
    cB
    cR
    cbs
    cfv
    #
    cX
    cB
    wcel
    cX
    cB
    cU
    cdif
    #
    cN
    cX
    cB
    cU
    eldifi
    irred.4
    eleq2s
    irred.1
    syl6eleq
    elfvexd
    adantr
    @1
    @0
    cX
    @5
    vz
    cv
    #
    wne
    #
    vy
    cN
    wral
    #
    vx
    cN
    wral
    #
    vz
    cN
    crab
    #
    wcel
    @8
    @1
    cI
    @18
    cX
    @1
    cI
    @11
    @18
    irred.3
    vr
    cR
    vb
    vr
    cv
    #
    cbs
    cfv
    #
    @19
    cui
    cfv
    #
    cdif
    #
    @3
    @4
    @19
    cmulr
    cfv
    #
    co
    #
    @14
    wne
    #
    vy
    vb
    cv
    #
    wral
    #
    vx
    @26
    wral
    #
    vz
    @26
    crab
    #
    csb
    @18
    cvv
    cir
    @19
    cR
    wceq
    #
    vb
    @22
    @29
    @18
    cvv
    @20
    cvv
    wcel
    @22
    cvv
    wcel
    @30
    @19
    cbs
    fvex
    @20
    @21
    cvv
    difexg
    mp1i
    @30
    @26
    @22
    wceq
    #
    wa
    #
    @28
    @17
    vz
    @26
    cN
    @32
    @26
    @22
    cN
    @30
    @31
    simpr
    @32
    @22
    @13
    cN
    @32
    @20
    cB
    @21
    cU
    @32
    @20
    @12
    cB
    @32
    @19
    cR
    cbs
    @30
    @31
    simpl
    #
    fveq2d
    irred.1
    syl6eqr
    @32
    @21
    cR
    cui
    cfv
    cU
    @32
    @19
    cR
    cui
    @33
    fveq2d
    irred.2
    syl6eqr
    difeq12d
    irred.4
    syl6eqr
    eqtrd
    #
    @32
    @27
    @16
    vx
    @26
    cN
    @34
    @32
    @25
    @15
    vy
    @26
    cN
    @34
    @32
    @24
    @5
    @14
    @32
    @23
    c.x
    @3
    @4
    @32
    @23
    cR
    cmulr
    cfv
    c.x
    @32
    @19
    cR
    cmulr
    @33
    fveq2d
    irred.5
    syl6eqr
    oveqd
    neeq1d
    raleqbidv
    raleqbidv
    rabeqbidv
    csbied
    vx
    vy
    vz
    vr
    vb
    df-irred
    @17
    vz
    cN
    cN
    @13
    cvv
    irred.4
    cB
    cvv
    wcel
    @13
    cvv
    wcel
    cB
    @12
    cvv
    irred.1
    cR
    cbs
    fvex
    eqeltri
    cB
    cU
    cvv
    difexg
    ax-mp
    eqeltri
    rabex
    fvmpt
    syl5eq
    eleq2d
    @17
    @7
    vz
    cX
    cN
    @14
    cX
    wceq
    @15
    @6
    vx
    vy
    cN
    cN
    @14
    cX
    @5
    neeq2
    2ralbidv
    elrab
    syl6bb
    pm5.21nii
end
