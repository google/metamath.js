include "cgrp.mm"
include "wcel.mm"
include "cec.mm"
include "c0g.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "cmpt.mm"
include "cqs.mm"
include "cvv.mm"
include "eqid.mm"
include "wer.mm"
include "cbs.mm"
include "fvex.mm"
include "syl6eqel.mm"
include "erex.mm"
include "sylc.mm"
include "qusval.mm"
include "quslem.mm"
include "co.mm"
include "3expb.mm"
include "ercpbl.mm"
include "w3a.mm"
include "adantr.mm"
include "erthi.mm"
include "divsfval.mm"
include "3eqtr4d.mm"
include "ersym.mm"
include "3eqtr4rd.mm"
include "imasgrp2.mm"
include "eqcomd.mm"
include "eqeq1d.mm"
include "anbi2d.mm"
include "mpbird.mm"

theorem qusgrp2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let c.pl: class .+
  let c.sm: class .~
  let cR: class R
  let cU: class U
  let cN: class N
  let cV: class V
  let cX: class X
  let c.0: class .0.
  let vq: setvar q
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let vu: setvar u
  assume qusgrp2.u: |- ( ph -> U = ( R /s .~ ) )
  assume qusgrp2.v: |- ( ph -> V = ( Base ` R ) )
  assume qusgrp2.p: |- ( ph -> .+ = ( +g ` R ) )
  assume qusgrp2.r: |- ( ph -> .~ Er V )
  assume qusgrp2.x: |- ( ph -> R e. X )
  assume qusgrp2.e: |- ( ph -> ( ( a .~ p /\ b .~ q ) -> ( a .+ b ) .~ ( p .+ q ) ) )
  assume qusgrp2.1: |- ( ( ph /\ x e. V /\ y e. V ) -> ( x .+ y ) e. V )
  assume qusgrp2.2: |- ( ( ph /\ ( x e. V /\ y e. V /\ z e. V ) ) -> ( ( x .+ y ) .+ z ) .~ ( x .+ ( y .+ z ) ) )
  assume qusgrp2.3: |- ( ph -> .0. e. V )
  assume qusgrp2.4: |- ( ( ph /\ x e. V ) -> ( .0. .+ x ) .~ x )
  assume qusgrp2.5: |- ( ( ph /\ x e. V ) -> N e. V )
  assume qusgrp2.6: |- ( ( ph /\ x e. V ) -> ( N .+ x ) .~ .0. )

  disjoint a b
  disjoint a p
  disjoint a q
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint .~ a
  disjoint b p
  disjoint b q
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint .~ b
  disjoint p q
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint .~ p
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint .~ q
  disjoint x y
  disjoint x z
  disjoint .~ x
  disjoint y z
  disjoint .~ y
  disjoint .~ z
  disjoint .0. a
  disjoint .0. b
  disjoint .0. p
  disjoint .0. q
  disjoint .0. x
  disjoint N p
  disjoint R p
  disjoint R q
  disjoint .+ a
  disjoint .+ b
  disjoint .+ p
  disjoint .+ q
  disjoint .+ x
  disjoint .+ y
  disjoint a ph
  disjoint b ph
  disjoint p ph
  disjoint ph q
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint V a
  disjoint V b
  disjoint V p
  disjoint V q
  disjoint V x
  disjoint V y
  disjoint V z
  disjoint U a
  disjoint U b
  disjoint U p
  disjoint U q
  disjoint U x
  disjoint U y
  disjoint U z
  disjoint a u
  disjoint b u
  disjoint p u
  disjoint q u
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint .~ u
  disjoint .0. u
  disjoint N u
  disjoint R u
  disjoint .+ u
  disjoint ph u
  disjoint V u
  assert |- ( ph -> ( U e. Grp /\ [ .0. ] .~ = ( 0g ` U ) ) )

  proof
    wph
    cU
    cgrp
    wcel
    #
    c.0
    c.sm
    cec
    #
    cU
    c0g
    cfv
    #
    wceq
    #
    wa
    @0
    c.0
    vu
    cV
    vu
    cv
    c.sm
    cec
    cmpt
    #
    cfv
    #
    @2
    wceq
    #
    wa
    wph
    vx
    vy
    vz
    cV
    c.sm
    cqs
    c.pl
    cR
    cU
    @4
    cN
    cV
    cX
    c.0
    vq
    vp
    va
    vb
    wph
    vu
    c.sm
    cR
    cU
    @4
    cV
    cvv
    cX
    qusgrp2.u
    qusgrp2.v
    @4
    eqid
    #
    wph
    cV
    c.sm
    wer
    #
    cV
    cvv
    wcel
    #
    c.sm
    cvv
    wcel
    qusgrp2.r
    wph
    cV
    cR
    cbs
    cfv
    cvv
    qusgrp2.v
    cR
    cbs
    fvex
    syl6eqel
    #
    cV
    c.sm
    cvv
    erex
    sylc
    #
    qusgrp2.x
    qusval
    qusgrp2.v
    qusgrp2.p
    wph
    vu
    c.sm
    cR
    cU
    @4
    cV
    cvv
    cX
    qusgrp2.u
    qusgrp2.v
    @7
    @11
    qusgrp2.x
    quslem
    wph
    vu
    va
    cv
    vb
    cv
    vp
    cv
    vq
    cv
    c.pl
    c.sm
    @4
    cV
    vx
    vy
    qusgrp2.r
    @10
    @7
    wph
    vx
    cv
    #
    cV
    wcel
    #
    vy
    cv
    #
    cV
    wcel
    #
    @12
    @14
    c.pl
    co
    #
    cV
    wcel
    qusgrp2.1
    3expb
    qusgrp2.e
    ercpbl
    qusgrp2.x
    qusgrp2.1
    wph
    @13
    @15
    vz
    cv
    #
    cV
    wcel
    w3a
    #
    wa
    #
    @16
    @17
    c.pl
    co
    #
    c.sm
    cec
    @12
    @14
    @17
    c.pl
    co
    c.pl
    co
    #
    c.sm
    cec
    @20
    @4
    cfv
    @21
    @4
    cfv
    @19
    @20
    @21
    c.sm
    cV
    wph
    @8
    @18
    qusgrp2.r
    adantr
    #
    qusgrp2.2
    erthi
    @19
    vu
    @20
    c.sm
    @4
    cV
    @22
    wph
    @9
    @18
    @10
    adantr
    #
    @7
    divsfval
    @19
    vu
    @21
    c.sm
    @4
    cV
    @22
    @23
    @7
    divsfval
    3eqtr4d
    qusgrp2.3
    wph
    @13
    wa
    #
    c.0
    @12
    c.pl
    co
    #
    c.sm
    cec
    @12
    c.sm
    cec
    @25
    @4
    cfv
    @12
    @4
    cfv
    @24
    @25
    @12
    c.sm
    cV
    wph
    @8
    @13
    qusgrp2.r
    adantr
    #
    qusgrp2.4
    erthi
    @24
    vu
    @25
    c.sm
    @4
    cV
    @26
    wph
    @9
    @13
    @10
    adantr
    #
    @7
    divsfval
    @24
    vu
    @12
    c.sm
    @4
    cV
    @26
    @27
    @7
    divsfval
    3eqtr4d
    qusgrp2.5
    @24
    @1
    cN
    @12
    c.pl
    co
    #
    c.sm
    cec
    @5
    @28
    @4
    cfv
    @24
    c.0
    @28
    c.sm
    cV
    @26
    @24
    @28
    c.0
    c.sm
    cV
    @26
    qusgrp2.6
    ersym
    erthi
    @24
    vu
    c.0
    c.sm
    @4
    cV
    @26
    @27
    @7
    divsfval
    @24
    vu
    @28
    c.sm
    @4
    cV
    @26
    @27
    @7
    divsfval
    3eqtr4rd
    imasgrp2
    wph
    @3
    @6
    @0
    wph
    @1
    @5
    @2
    wph
    @5
    @1
    wph
    vu
    c.0
    c.sm
    @4
    cV
    qusgrp2.r
    @10
    @7
    divsfval
    eqcomd
    eqeq1d
    anbi2d
    mpbird
end
