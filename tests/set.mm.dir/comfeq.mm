include "cv.mm"
include "cop.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "cxp.mm"
include "c2nd.mm"
include "cfv.mm"
include "cmpt2.mm"
include "ccomf.mm"
include "cvv.mm"
include "wcel.mm"
include "wb.mm"
include "ovex.mm"
include "fvex.mm"
include "mpt2ex.mm"
include "rgen2w.mm"
include "mpt22eqb.mm"
include "ax-mp.mm"
include "vex.mm"
include "op2ndd.mm"
include "oveq1d.mm"
include "fveq2.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "oveq1.mm"
include "oveqd.mm"
include "eqeq12d.mm"
include "raleqbidv.mm"
include "ralcom.mm"
include "3bitr4g.mm"
include "ralbidv.mm"
include "ralxp.mm"
include "bitri.mm"
include "cbs.mm"
include "sqxpeqd.mm"
include "eqidd.mm"
include "mpt2eq123dv.mm"
include "eqid.mm"
include "comfffval.mm"
include "chom.mm"
include "w3a.mm"
include "chomf.mm"
include "3ad2ant1.mm"
include "xp2nd.mm"
include "3ad2ant2.mm"
include "eleqtrd.mm"
include "simp3.mm"
include "homfeqval.mm"
include "c1st.mm"
include "xp1st.mm"
include "3eqtr3g.mm"
include "1st2nd2.mm"
include "fveq2d.mm"
include "3eqtr4d.mm"
include "mpt2eq3dva.mm"
include "eqtrd.mm"
include "syl5rbbr.mm"

theorem comfeq
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cD: class D
  let c.xb: class .xb
  let c.x: class .x.
  let vf: setvar f
  let vg: setvar g
  let cH: class H
  let vu: setvar u
  assume comfeq.1: |- .x. = ( comp ` C )
  assume comfeq.2: |- .xb = ( comp ` D )
  assume comfeq.h: |- H = ( Hom ` C )
  assume comfeq.3: |- ( ph -> B = ( Base ` C ) )
  assume comfeq.4: |- ( ph -> B = ( Base ` D ) )
  assume comfeq.5: |- ( ph -> ( Homf ` C ) = ( Homf ` D ) )

  disjoint f g
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint B f
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint B g
  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint C f
  disjoint C g
  disjoint C z
  disjoint f ph
  disjoint g ph
  disjoint ph z
  disjoint .x. f
  disjoint .x. g
  disjoint .x. x
  disjoint .x. y
  disjoint D f
  disjoint D g
  disjoint D z
  disjoint H f
  disjoint H g
  disjoint H x
  disjoint H y
  disjoint .xb f
  disjoint .xb g
  disjoint .xb x
  disjoint .xb y
  disjoint f u
  disjoint g u
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint B u
  disjoint C u
  disjoint ph u
  disjoint .x. u
  disjoint D u
  disjoint H u
  disjoint .xb u
  assert |- ( ph -> ( ( comf ` C ) = ( comf ` D ) <-> A. x e. B A. y e. B A. z e. B A. f e. ( x H y ) A. g e. ( y H z ) ( g ( <. x , y >. .x. z ) f ) = ( g ( <. x , y >. .xb z ) f ) ) )

  proof
    vg
    cv
    #
    vf
    cv
    #
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    vz
    cv
    #
    c.x
    co
    #
    co
    #
    @0
    @1
    @4
    @5
    c.xb
    co
    #
    co
    #
    wceq
    #
    vg
    @3
    @5
    cH
    co
    #
    wral
    vf
    @2
    @3
    cH
    co
    #
    wral
    #
    vz
    cB
    wral
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    vu
    vz
    cB
    cB
    cxp
    #
    cB
    vg
    vf
    vu
    cv
    #
    c2nd
    cfv
    #
    @5
    cH
    co
    #
    @17
    cH
    cfv
    #
    @0
    @1
    @17
    @5
    c.x
    co
    #
    co
    #
    cmpt2
    #
    cmpt2
    #
    vu
    vz
    @16
    cB
    vg
    vf
    @19
    @20
    @0
    @1
    @17
    @5
    c.xb
    co
    #
    co
    #
    cmpt2
    #
    cmpt2
    #
    wceq
    #
    wph
    cC
    ccomf
    cfv
    #
    cD
    ccomf
    cfv
    #
    wceq
    @29
    @23
    @27
    wceq
    #
    vz
    cB
    wral
    #
    vu
    @16
    wral
    #
    @15
    @23
    cvv
    wcel
    #
    vz
    cB
    wral
    vu
    @16
    wral
    @29
    @34
    wb
    @35
    vu
    vz
    @16
    cB
    vg
    vf
    @19
    @20
    @22
    @18
    @5
    cH
    ovex
    @17
    cH
    fvex
    mpt2ex
    rgen2w
    vu
    vz
    @16
    cB
    @23
    @27
    cvv
    mpt22eqb
    ax-mp
    @33
    @14
    vu
    vx
    vy
    cB
    cB
    @17
    @4
    wceq
    #
    @32
    @13
    vz
    cB
    @36
    @22
    @26
    wceq
    #
    vf
    @20
    wral
    #
    vg
    @19
    wral
    #
    @10
    vf
    @12
    wral
    #
    vg
    @11
    wral
    @32
    @13
    @36
    @38
    @40
    vg
    @19
    @11
    @36
    @18
    @3
    @5
    cH
    @2
    @3
    @17
    vx
    vex
    vy
    vex
    op2ndd
    oveq1d
    @36
    @37
    @10
    vf
    @20
    @12
    @36
    @20
    @4
    cH
    cfv
    @12
    @17
    @4
    cH
    fveq2
    @2
    @3
    cH
    df-ov
    syl6eqr
    @36
    @22
    @7
    @26
    @9
    @36
    @21
    @6
    @0
    @1
    @17
    @4
    @5
    c.x
    oveq1
    oveqd
    @36
    @25
    @8
    @0
    @1
    @17
    @4
    @5
    c.xb
    oveq1
    oveqd
    eqeq12d
    raleqbidv
    raleqbidv
    @22
    cvv
    wcel
    #
    vf
    @20
    wral
    vg
    @19
    wral
    @32
    @39
    wb
    @41
    vg
    vf
    @19
    @20
    @0
    @1
    @21
    ovex
    rgen2w
    vg
    vf
    @19
    @20
    @22
    @26
    cvv
    mpt22eqb
    ax-mp
    @10
    vf
    vg
    @12
    @11
    ralcom
    3bitr4g
    ralbidv
    ralxp
    bitri
    wph
    @24
    @30
    @28
    @31
    wph
    @24
    vu
    vz
    cC
    cbs
    cfv
    #
    @42
    cxp
    #
    @42
    @23
    cmpt2
    @30
    wph
    vu
    vz
    @16
    cB
    @23
    @43
    @42
    @23
    wph
    cB
    @42
    comfeq.3
    sqxpeqd
    comfeq.3
    wph
    @23
    eqidd
    mpt2eq123dv
    vu
    vz
    @42
    cC
    c.x
    vf
    vg
    cH
    @30
    @30
    eqid
    @42
    eqid
    #
    comfeq.h
    comfeq.1
    comfffval
    syl6eqr
    wph
    @28
    vu
    vz
    cD
    cbs
    cfv
    #
    @45
    cxp
    #
    @45
    vg
    vf
    @18
    @5
    cD
    chom
    cfv
    #
    co
    #
    @17
    @47
    cfv
    #
    @26
    cmpt2
    #
    cmpt2
    #
    @31
    wph
    @28
    vu
    vz
    @16
    cB
    @50
    cmpt2
    @51
    wph
    vu
    vz
    @16
    cB
    @27
    @50
    wph
    @17
    @16
    wcel
    #
    @5
    cB
    wcel
    #
    w3a
    #
    vg
    vf
    @19
    @20
    @26
    @48
    @49
    @26
    @54
    @42
    cC
    cD
    cH
    @47
    @18
    @5
    @44
    comfeq.h
    @47
    eqid
    #
    wph
    @52
    cC
    chomf
    cfv
    cD
    chomf
    cfv
    wceq
    @53
    comfeq.5
    3ad2ant1
    #
    @54
    @18
    cB
    @42
    @52
    wph
    @18
    cB
    wcel
    @53
    @17
    cB
    cB
    xp2nd
    3ad2ant2
    wph
    @52
    cB
    @42
    wceq
    @53
    comfeq.3
    3ad2ant1
    #
    eleqtrd
    #
    @54
    @5
    cB
    @42
    wph
    @52
    @53
    simp3
    @57
    eleqtrd
    homfeqval
    @54
    @17
    c1st
    cfv
    #
    @18
    cop
    #
    cH
    cfv
    #
    @60
    @47
    cfv
    #
    @20
    @49
    @54
    @59
    @18
    cH
    co
    @59
    @18
    @47
    co
    @61
    @62
    @54
    @42
    cC
    cD
    cH
    @47
    @59
    @18
    @44
    comfeq.h
    @55
    @56
    @54
    @59
    cB
    @42
    @52
    wph
    @59
    cB
    wcel
    @53
    @17
    cB
    cB
    xp1st
    3ad2ant2
    @57
    eleqtrd
    @58
    homfeqval
    @59
    @18
    cH
    df-ov
    @59
    @18
    @47
    df-ov
    3eqtr3g
    @54
    @17
    @60
    cH
    @52
    wph
    @17
    @60
    wceq
    @53
    @17
    cB
    cB
    1st2nd2
    3ad2ant2
    #
    fveq2d
    @54
    @17
    @60
    @47
    @63
    fveq2d
    3eqtr4d
    @54
    @26
    eqidd
    mpt2eq123dv
    mpt2eq3dva
    wph
    vu
    vz
    @16
    cB
    @50
    @46
    @45
    @50
    wph
    cB
    @45
    comfeq.4
    sqxpeqd
    comfeq.4
    wph
    @50
    eqidd
    mpt2eq123dv
    eqtrd
    vu
    vz
    @45
    cD
    c.xb
    vf
    vg
    @47
    @31
    @31
    eqid
    @45
    eqid
    @55
    comfeq.2
    comfffval
    syl6eqr
    eqeq12d
    syl5rbbr
end
