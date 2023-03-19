include "crg.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
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
include "wf.mm"
include "abvfval.mm"
include "eleq2d.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "bibi1d.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "breq12d.mm"
include "anbi12d.mm"
include "ralbidv.mm"
include "elrab.mm"
include "ovex.mm"
include "cbs.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "elmap.mm"
include "anbi1i.mm"
include "bitri.mm"
include "syl6bb.mm"

theorem isabv
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cR: class R
  let c.x: class .x.
  let cF: class F
  let c.0: class .0.
  let vf: setvar f
  let vr: setvar r
  assume abvfval.a: |- A = ( AbsVal ` R )
  assume abvfval.b: |- B = ( Base ` R )
  assume abvfval.p: |- .+ = ( +g ` R )
  assume abvfval.t: |- .x. = ( .r ` R )
  assume abvfval.z: |- .0. = ( 0g ` R )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint F x
  disjoint F y
  disjoint R x
  disjoint R y
  disjoint f r
  disjoint f x
  disjoint f y
  disjoint B f
  disjoint r x
  disjoint r y
  disjoint B r
  disjoint F f
  disjoint .+ f
  disjoint .+ r
  disjoint R f
  disjoint R r
  disjoint .x. f
  disjoint .x. r
  disjoint .0. f
  disjoint .0. r
  assert |- ( R e. Ring -> ( F e. A <-> ( F : B --> ( 0 [,) +oo ) /\ A. x e. B ( ( ( F ` x ) = 0 <-> x = .0. ) /\ A. y e. B ( ( F ` ( x .x. y ) ) = ( ( F ` x ) x. ( F ` y ) ) /\ ( F ` ( x .+ y ) ) <_ ( ( F ` x ) + ( F ` y ) ) ) ) ) ) )

  proof
    cR
    crg
    wcel
    #
    cF
    cA
    wcel
    cF
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
    @1
    c.0
    wceq
    #
    wb
    #
    @1
    vy
    cv
    #
    c.x
    co
    #
    @2
    cfv
    #
    @3
    @7
    @2
    cfv
    #
    cmul
    co
    #
    wceq
    #
    @1
    @7
    c.pl
    co
    #
    @2
    cfv
    #
    @3
    @10
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
    wcel
    #
    cB
    @21
    cF
    wf
    #
    @1
    cF
    cfv
    #
    cc0
    wceq
    #
    @5
    wb
    #
    @8
    cF
    cfv
    #
    @26
    @7
    cF
    cfv
    #
    cmul
    co
    #
    wceq
    #
    @13
    cF
    cfv
    #
    @26
    @30
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
    wa
    #
    @0
    cA
    @23
    cF
    vx
    vy
    cA
    cB
    c.pl
    cR
    c.x
    vf
    c.0
    abvfval.a
    abvfval.b
    abvfval.p
    abvfval.t
    abvfval.z
    abvfval
    eleq2d
    @24
    cF
    @22
    wcel
    #
    @39
    wa
    @40
    @20
    @39
    vf
    cF
    @22
    @2
    cF
    wceq
    #
    @19
    @38
    vx
    cB
    @42
    @6
    @28
    @18
    @37
    @42
    @4
    @27
    @5
    @42
    @3
    @26
    cc0
    @1
    @2
    cF
    fveq1
    #
    eqeq1d
    bibi1d
    @42
    @17
    @36
    vy
    cB
    @42
    @12
    @32
    @16
    @35
    @42
    @9
    @29
    @11
    @31
    @8
    @2
    cF
    fveq1
    @42
    @3
    @26
    @10
    @30
    cmul
    @43
    @7
    @2
    cF
    fveq1
    #
    oveq12d
    eqeq12d
    @42
    @14
    @33
    @15
    @34
    cle
    @13
    @2
    cF
    fveq1
    @42
    @3
    @26
    @10
    @30
    caddc
    @43
    @44
    oveq12d
    breq12d
    anbi12d
    ralbidv
    anbi12d
    ralbidv
    elrab
    @41
    @25
    @39
    @21
    cB
    cF
    cc0
    cpnf
    cico
    ovex
    cB
    cR
    cbs
    cfv
    cvv
    abvfval.b
    cR
    cbs
    fvex
    eqeltri
    elmap
    anbi1i
    bitri
    syl6bb
end
