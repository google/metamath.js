include "crg.mm"
include "wcel.mm"
include "cabv.mm"
include "cfv.mm"
include "cv.mm"
include "cc0.mm"
include "wceq.mm"
include "wb.mm"
include "co.mm"
include "cmul.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "wral.mm"
include "cpnf.mm"
include "cico.mm"
include "cmap.mm"
include "crab.mm"
include "c0g.mm"
include "cmulr.mm"
include "cplusg.mm"
include "cbs.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "oveq2d.mm"
include "eqeq2d.mm"
include "bibi2d.mm"
include "oveqd.mm"
include "fveq2d.mm"
include "eqeq1d.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "raleqbidv.mm"
include "rabeqbidv.mm"
include "df-abv.mm"
include "ovex.mm"
include "rabex.mm"
include "fvmpt.mm"
include "syl5eq.mm"

theorem abvfval
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cR: class R
  let c.x: class .x.
  let vf: setvar f
  let c.0: class .0.
  let vr: setvar r
  let cF: class F
  assume abvfval.a: |- A = ( AbsVal ` R )
  assume abvfval.b: |- B = ( Base ` R )
  assume abvfval.p: |- .+ = ( +g ` R )
  assume abvfval.t: |- .x. = ( .r ` R )
  assume abvfval.z: |- .0. = ( 0g ` R )

  disjoint f x
  disjoint f y
  disjoint B f
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint .+ f
  disjoint R f
  disjoint R x
  disjoint R y
  disjoint .x. f
  disjoint .0. f
  disjoint f r
  disjoint r x
  disjoint r y
  disjoint B r
  disjoint F f
  disjoint F x
  disjoint F y
  disjoint .+ r
  disjoint R r
  disjoint .x. r
  disjoint .0. r
  assert |- ( R e. Ring -> A = { f e. ( ( 0 [,) +oo ) ^m B ) | A. x e. B ( ( ( f ` x ) = 0 <-> x = .0. ) /\ A. y e. B ( ( f ` ( x .x. y ) ) = ( ( f ` x ) x. ( f ` y ) ) /\ ( f ` ( x .+ y ) ) <_ ( ( f ` x ) + ( f ` y ) ) ) ) } )

  proof
    cR
    crg
    wcel
    cA
    cR
    cabv
    cfv
    vx
    cv
    #
    vf
    cv
    #
    cfv
    #
    cc0
    wceq
    #
    @0
    c.0
    wceq
    #
    wb
    #
    @0
    vy
    cv
    #
    c.x
    co
    #
    @1
    cfv
    #
    @2
    @6
    @1
    cfv
    #
    cmul
    co
    #
    wceq
    #
    @0
    @6
    c.pl
    co
    #
    @1
    cfv
    #
    @2
    @9
    caddc
    co
    #
    cle
    wbr
    #
    wa
    #
    vy
    cB
    wral
    #
    wa
    #
    vx
    cB
    wral
    #
    vf
    cc0
    cpnf
    cico
    co
    #
    cB
    cmap
    co
    #
    crab
    #
    abvfval.a
    vr
    cR
    @3
    @0
    vr
    cv
    #
    c0g
    cfv
    #
    wceq
    #
    wb
    #
    @0
    @6
    @23
    cmulr
    cfv
    #
    co
    #
    @1
    cfv
    #
    @10
    wceq
    #
    @0
    @6
    @23
    cplusg
    cfv
    #
    co
    #
    @1
    cfv
    #
    @14
    cle
    wbr
    #
    wa
    #
    vy
    @23
    cbs
    cfv
    #
    wral
    #
    wa
    #
    vx
    @36
    wral
    #
    vf
    @20
    @36
    cmap
    co
    #
    crab
    @22
    crg
    cabv
    @23
    cR
    wceq
    #
    @39
    @19
    vf
    @40
    @21
    @41
    @36
    cB
    @20
    cmap
    @41
    @36
    cR
    cbs
    cfv
    cB
    @23
    cR
    cbs
    fveq2
    abvfval.b
    syl6eqr
    #
    oveq2d
    @41
    @38
    @18
    vx
    @36
    cB
    @42
    @41
    @26
    @5
    @37
    @17
    @41
    @25
    @4
    @3
    @41
    @24
    c.0
    @0
    @41
    @24
    cR
    c0g
    cfv
    c.0
    @23
    cR
    c0g
    fveq2
    abvfval.z
    syl6eqr
    eqeq2d
    bibi2d
    @41
    @35
    @16
    vy
    @36
    cB
    @42
    @41
    @30
    @11
    @34
    @15
    @41
    @29
    @8
    @10
    @41
    @28
    @7
    @1
    @41
    @27
    c.x
    @0
    @6
    @41
    @27
    cR
    cmulr
    cfv
    c.x
    @23
    cR
    cmulr
    fveq2
    abvfval.t
    syl6eqr
    oveqd
    fveq2d
    eqeq1d
    @41
    @33
    @13
    @14
    cle
    @41
    @32
    @12
    @1
    @41
    @31
    c.pl
    @0
    @6
    @41
    @31
    cR
    cplusg
    cfv
    c.pl
    @23
    cR
    cplusg
    fveq2
    abvfval.p
    syl6eqr
    oveqd
    fveq2d
    breq1d
    anbi12d
    raleqbidv
    anbi12d
    raleqbidv
    rabeqbidv
    vx
    vy
    vf
    vr
    df-abv
    @19
    vf
    @21
    @20
    cB
    cmap
    ovex
    rabex
    fvmpt
    syl5eq
end
