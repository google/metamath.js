include "cga.mm"
include "co.mm"
include "wcel.mm"
include "cgrp.mm"
include "cvv.mm"
include "wa.mm"
include "cxp.mm"
include "wf.mm"
include "cv.mm"
include "wceq.mm"
include "wral.mm"
include "cbs.mm"
include "cfv.mm"
include "c0g.mm"
include "cplusg.mm"
include "cmap.mm"
include "crab.mm"
include "csb.mm"
include "df-ga.mm"
include "elmpt2cl.mm"
include "fvexd.mm"
include "simplr.mm"
include "id.mm"
include "simpl.mm"
include "fveq2d.mm"
include "syl6eqr.mm"
include "sylan9eqr.mm"
include "xpeq12d.mm"
include "oveq12d.mm"
include "simpll.mm"
include "oveq1d.mm"
include "eqeq1d.mm"
include "oveqd.mm"
include "raleqbidv.mm"
include "anbi12d.mm"
include "rabeqbidv.mm"
include "csbied.mm"
include "ovex.mm"
include "rabex.mm"
include "ovmpt2a.mm"
include "eleq2d.mm"
include "oveq.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "eqeq12d.mm"
include "2ralbidv.mm"
include "ralbidv.mm"
include "elrab.mm"
include "syl6bb.mm"
include "simpr.mm"
include "fvex.mm"
include "eqeltri.mm"
include "xpexg.mm"
include "sylancr.mm"
include "elmapd.mm"
include "anbi1d.mm"
include "bitrd.mm"
include "biadan2.mm"

theorem isga
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let c.pl: class .+
  let c.po: class .(+)
  let cG: class G
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vb: setvar b
  let vg: setvar g
  let vm: setvar m
  let vs: setvar s
  assume isga.1: |- X = ( Base ` G )
  assume isga.2: |- .+ = ( +g ` G )
  assume isga.3: |- .0. = ( 0g ` G )

  disjoint x y
  disjoint x z
  disjoint G x
  disjoint y z
  disjoint G y
  disjoint G z
  disjoint X y
  disjoint X z
  disjoint Y x
  disjoint Y y
  disjoint Y z
  disjoint .(+) x
  disjoint .(+) y
  disjoint .(+) z
  disjoint b g
  disjoint b m
  disjoint b s
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint G b
  disjoint g m
  disjoint g s
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint G g
  disjoint m s
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint G m
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint G s
  disjoint X b
  disjoint X g
  disjoint X m
  disjoint X s
  disjoint Y b
  disjoint Y g
  disjoint Y m
  disjoint Y s
  disjoint .+ b
  disjoint .+ g
  disjoint .+ m
  disjoint .+ s
  disjoint .(+) m
  disjoint .0. b
  disjoint .0. g
  disjoint .0. m
  disjoint .0. s
  assert |- ( .(+) e. ( G GrpAct Y ) <-> ( ( G e. Grp /\ Y e. _V ) /\ ( .(+) : ( X X. Y ) --> Y /\ A. x e. Y ( ( .0. .(+) x ) = x /\ A. y e. X A. z e. X ( ( y .+ z ) .(+) x ) = ( y .(+) ( z .(+) x ) ) ) ) ) )

  proof
    c.po
    cG
    cY
    cga
    co
    #
    wcel
    #
    cG
    cgrp
    wcel
    #
    cY
    cvv
    wcel
    #
    wa
    #
    cX
    cY
    cxp
    #
    cY
    c.po
    wf
    #
    c.0
    vx
    cv
    #
    c.po
    co
    #
    @7
    wceq
    #
    vy
    cv
    #
    vz
    cv
    #
    c.pl
    co
    #
    @7
    c.po
    co
    #
    @10
    @11
    @7
    c.po
    co
    #
    c.po
    co
    #
    wceq
    #
    vz
    cX
    wral
    vy
    cX
    wral
    #
    wa
    #
    vx
    cY
    wral
    #
    wa
    #
    vg
    vs
    cgrp
    cvv
    vb
    vg
    cv
    #
    cbs
    cfv
    #
    @21
    c0g
    cfv
    #
    @7
    vm
    cv
    #
    co
    #
    @7
    wceq
    #
    @10
    @11
    @21
    cplusg
    cfv
    #
    co
    #
    @7
    @24
    co
    #
    @10
    @11
    @7
    @24
    co
    #
    @24
    co
    #
    wceq
    #
    vz
    vb
    cv
    #
    wral
    #
    vy
    @33
    wral
    #
    wa
    #
    vx
    vs
    cv
    #
    wral
    #
    vm
    @37
    @33
    @37
    cxp
    #
    cmap
    co
    #
    crab
    #
    csb
    #
    cG
    cY
    cga
    c.po
    vx
    vy
    vz
    vg
    vm
    vs
    vb
    df-ga
    #
    elmpt2cl
    @4
    @1
    c.po
    cY
    @5
    cmap
    co
    #
    wcel
    #
    @19
    wa
    #
    @20
    @4
    @1
    c.po
    c.0
    @7
    @24
    co
    #
    @7
    wceq
    #
    @12
    @7
    @24
    co
    #
    @31
    wceq
    #
    vz
    cX
    wral
    #
    vy
    cX
    wral
    #
    wa
    #
    vx
    cY
    wral
    #
    vm
    @44
    crab
    #
    wcel
    @46
    @4
    @0
    @55
    c.po
    vg
    vs
    cG
    cY
    cgrp
    cvv
    @42
    @55
    cga
    @21
    cG
    wceq
    #
    @37
    cY
    wceq
    #
    wa
    #
    vb
    @22
    @41
    @55
    cvv
    @58
    @21
    cbs
    fvexd
    @58
    @33
    @22
    wceq
    #
    wa
    #
    @38
    @54
    vm
    @40
    @44
    @60
    @37
    cY
    @39
    @5
    cmap
    @56
    @57
    @59
    simplr
    #
    @60
    @33
    cX
    @37
    cY
    @59
    @58
    @33
    @22
    cX
    @59
    id
    @58
    @22
    cG
    cbs
    cfv
    #
    cX
    @58
    @21
    cG
    cbs
    @56
    @57
    simpl
    fveq2d
    isga.1
    syl6eqr
    sylan9eqr
    #
    @61
    xpeq12d
    oveq12d
    @60
    @36
    @53
    vx
    @37
    cY
    @61
    @60
    @26
    @48
    @35
    @52
    @60
    @25
    @47
    @7
    @60
    @23
    c.0
    @7
    @24
    @60
    @23
    cG
    c0g
    cfv
    c.0
    @60
    @21
    cG
    c0g
    @56
    @57
    @59
    simpll
    #
    fveq2d
    isga.3
    syl6eqr
    oveq1d
    eqeq1d
    @60
    @34
    @51
    vy
    @33
    cX
    @63
    @60
    @32
    @50
    vz
    @33
    cX
    @63
    @60
    @29
    @49
    @31
    @60
    @28
    @12
    @7
    @24
    @60
    @27
    c.pl
    @10
    @11
    @60
    @27
    cG
    cplusg
    cfv
    c.pl
    @60
    @21
    cG
    cplusg
    @64
    fveq2d
    isga.2
    syl6eqr
    oveqd
    oveq1d
    eqeq1d
    raleqbidv
    raleqbidv
    anbi12d
    raleqbidv
    rabeqbidv
    csbied
    @43
    @54
    vm
    @44
    cY
    @5
    cmap
    ovex
    rabex
    ovmpt2a
    eleq2d
    @54
    @19
    vm
    c.po
    @44
    @24
    c.po
    wceq
    #
    @53
    @18
    vx
    cY
    @65
    @48
    @9
    @52
    @17
    @65
    @47
    @8
    @7
    c.0
    @7
    @24
    c.po
    oveq
    eqeq1d
    @65
    @50
    @16
    vy
    vz
    cX
    cX
    @65
    @49
    @13
    @31
    @15
    @12
    @7
    @24
    c.po
    oveq
    @65
    @31
    @10
    @30
    c.po
    co
    @15
    @10
    @30
    @24
    c.po
    oveq
    @65
    @30
    @14
    @10
    c.po
    @11
    @7
    @24
    c.po
    oveq
    oveq2d
    eqtrd
    eqeq12d
    2ralbidv
    anbi12d
    ralbidv
    elrab
    syl6bb
    @4
    @45
    @6
    @19
    @4
    cY
    @5
    c.po
    cvv
    cvv
    @2
    @3
    simpr
    #
    @4
    cX
    cvv
    wcel
    @3
    @5
    cvv
    wcel
    cX
    @62
    cvv
    isga.1
    cG
    cbs
    fvex
    eqeltri
    @66
    cX
    cY
    cvv
    cvv
    xpexg
    sylancr
    elmapd
    anbi1d
    bitrd
    biadan2
end
