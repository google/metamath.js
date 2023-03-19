include "ccomf.mm"
include "cfv.mm"
include "cxp.mm"
include "cv.mm"
include "c2nd.mm"
include "co.mm"
include "cmpt2.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "cbs.mm"
include "chom.mm"
include "cco.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "sqxpeqd.mm"
include "oveqd.mm"
include "fveq1d.mm"
include "mpt2eq123dv.mm"
include "df-comf.mm"
include "fvex.mm"
include "eqeltri.mm"
include "xpex.mm"
include "mpt2ex.mm"
include "fvmpt.mm"
include "wn.mm"
include "c0.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "xpeq2d.mm"
include "xp0.mm"
include "syl6eq.mm"
include "mpt2eq12.mm"
include "syl2anc.mm"
include "mpt20.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"
include "eqtri.mm"

theorem comfffval
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let c.x: class .x.
  let vf: setvar f
  let vg: setvar g
  let cH: class H
  let cO: class O
  let vc: setvar c
  let vz: setvar z
  let wph: wff ph
  let cF: class F
  let cG: class G
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume comfffval.o: |- O = ( comf ` C )
  assume comfffval.b: |- B = ( Base ` C )
  assume comfffval.h: |- H = ( Hom ` C )
  assume comfffval.x: |- .x. = ( comp ` C )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint f g
  disjoint f x
  disjoint f y
  disjoint C f
  disjoint g x
  disjoint g y
  disjoint C g
  disjoint C x
  disjoint C y
  disjoint .x. f
  disjoint .x. g
  disjoint .x. x
  disjoint H f
  disjoint H g
  disjoint H x
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint B c
  disjoint x z
  disjoint y z
  disjoint B z
  disjoint c f
  disjoint c g
  disjoint C c
  disjoint f z
  disjoint g z
  disjoint C z
  disjoint f ph
  disjoint g ph
  disjoint ph x
  disjoint ph z
  disjoint .x. c
  disjoint .x. z
  disjoint F f
  disjoint F g
  disjoint G f
  disjoint G g
  disjoint X f
  disjoint X g
  disjoint X x
  disjoint X z
  disjoint Y f
  disjoint Y g
  disjoint Y x
  disjoint Y z
  disjoint Z f
  disjoint Z g
  disjoint Z x
  disjoint Z z
  disjoint H c
  disjoint H z
  assert |- O = ( x e. ( B X. B ) , y e. B |-> ( g e. ( ( 2nd ` x ) H y ) , f e. ( H ` x ) |-> ( g ( x .x. y ) f ) ) )

  proof
    cO
    cC
    ccomf
    cfv
    #
    vx
    vy
    cB
    cB
    cxp
    #
    cB
    vg
    vf
    vx
    cv
    #
    c2nd
    cfv
    #
    vy
    cv
    #
    cH
    co
    #
    @2
    cH
    cfv
    #
    vg
    cv
    #
    vf
    cv
    #
    @2
    @4
    c.x
    co
    #
    co
    #
    cmpt2
    #
    cmpt2
    #
    comfffval.o
    cC
    cvv
    wcel
    #
    @0
    @12
    wceq
    vc
    cC
    vx
    vy
    vc
    cv
    #
    cbs
    cfv
    #
    @15
    cxp
    #
    @15
    vg
    vf
    @3
    @4
    @14
    chom
    cfv
    #
    co
    #
    @2
    @17
    cfv
    #
    @7
    @8
    @2
    @4
    @14
    cco
    cfv
    #
    co
    #
    co
    #
    cmpt2
    #
    cmpt2
    @12
    cvv
    ccomf
    @14
    cC
    wceq
    #
    vx
    vy
    @16
    @15
    @23
    @1
    cB
    @11
    @24
    @15
    cB
    @24
    @15
    cC
    cbs
    cfv
    #
    cB
    @14
    cC
    cbs
    fveq2
    comfffval.b
    syl6eqr
    #
    sqxpeqd
    @26
    @24
    vg
    vf
    @18
    @19
    @22
    @5
    @6
    @10
    @24
    @17
    cH
    @3
    @4
    @24
    @17
    cC
    chom
    cfv
    cH
    @14
    cC
    chom
    fveq2
    comfffval.h
    syl6eqr
    #
    oveqd
    @24
    @2
    @17
    cH
    @27
    fveq1d
    @24
    @21
    @9
    @7
    @8
    @24
    @20
    c.x
    @2
    @4
    @24
    @20
    cC
    cco
    cfv
    c.x
    @14
    cC
    cco
    fveq2
    comfffval.x
    syl6eqr
    oveqd
    oveqd
    mpt2eq123dv
    mpt2eq123dv
    vx
    vy
    vf
    vg
    vc
    df-comf
    vx
    vy
    @1
    cB
    @11
    cB
    cB
    cB
    @25
    cvv
    comfffval.b
    cC
    cbs
    fvex
    eqeltri
    #
    @28
    xpex
    @28
    mpt2ex
    fvmpt
    @13
    wn
    #
    @0
    c0
    @12
    cC
    ccomf
    fvprc
    @29
    @12
    vx
    vy
    c0
    c0
    @11
    cmpt2
    #
    c0
    @29
    @1
    c0
    wceq
    cB
    c0
    wceq
    @12
    @30
    wceq
    @29
    @1
    cB
    c0
    cxp
    c0
    @29
    cB
    c0
    cB
    @29
    cB
    @25
    c0
    comfffval.b
    cC
    cbs
    fvprc
    syl5eq
    #
    xpeq2d
    cB
    xp0
    syl6eq
    @31
    vx
    vy
    @1
    cB
    c0
    c0
    @11
    mpt2eq12
    syl2anc
    vx
    vy
    c0
    @11
    mpt20
    syl6eq
    eqtr4d
    pm2.61i
    eqtri
end
