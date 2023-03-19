include "crlreg.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "crab.mm"
include "cvv.mm"
include "wcel.mm"
include "cmulr.mm"
include "c0g.mm"
include "cbs.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "oveqd.mm"
include "eqeq12d.mm"
include "eqeq2d.mm"
include "imbi12d.mm"
include "raleqbidv.mm"
include "rabeqbidv.mm"
include "df-rlreg.mm"
include "fvex.mm"
include "eqeltri.mm"
include "rabex.mm"
include "fvmpt.mm"
include "wn.mm"
include "c0.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "rabeq.mm"
include "syl.mm"
include "rab0.mm"
include "syl6eq.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"
include "eqtri.mm"

theorem rrgval
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let cE: class E
  let c.0: class .0.
  let vr: setvar r
  assume rrgval.e: |- E = ( RLReg ` R )
  assume rrgval.b: |- B = ( Base ` R )
  assume rrgval.t: |- .x. = ( .r ` R )
  assume rrgval.z: |- .0. = ( 0g ` R )

  disjoint B x
  disjoint B y
  disjoint x y
  disjoint R x
  disjoint R y
  disjoint B r
  disjoint r x
  disjoint r y
  disjoint R r
  disjoint .x. r
  disjoint .0. r
  assert |- E = { x e. B | A. y e. B ( ( x .x. y ) = .0. -> y = .0. ) }

  proof
    cE
    cR
    crlreg
    cfv
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
    c.0
    wceq
    #
    @2
    c.0
    wceq
    #
    wi
    #
    vy
    cB
    wral
    #
    vx
    cB
    crab
    #
    rrgval.e
    cR
    cvv
    wcel
    #
    @0
    @8
    wceq
    vr
    cR
    @1
    @2
    vr
    cv
    #
    cmulr
    cfv
    #
    co
    #
    @10
    c0g
    cfv
    #
    wceq
    #
    @2
    @13
    wceq
    #
    wi
    #
    vy
    @10
    cbs
    cfv
    #
    wral
    #
    vx
    @17
    crab
    @8
    cvv
    crlreg
    @10
    cR
    wceq
    #
    @18
    @7
    vx
    @17
    cB
    @19
    @17
    cR
    cbs
    cfv
    #
    cB
    @10
    cR
    cbs
    fveq2
    rrgval.b
    syl6eqr
    #
    @19
    @16
    @6
    vy
    @17
    cB
    @21
    @19
    @14
    @4
    @15
    @5
    @19
    @12
    @3
    @13
    c.0
    @19
    @11
    c.x
    @1
    @2
    @19
    @11
    cR
    cmulr
    cfv
    c.x
    @10
    cR
    cmulr
    fveq2
    rrgval.t
    syl6eqr
    oveqd
    @19
    @13
    cR
    c0g
    cfv
    c.0
    @10
    cR
    c0g
    fveq2
    rrgval.z
    syl6eqr
    #
    eqeq12d
    @19
    @13
    c.0
    @2
    @22
    eqeq2d
    imbi12d
    raleqbidv
    rabeqbidv
    vx
    vy
    vr
    df-rlreg
    @7
    vx
    cB
    cB
    @20
    cvv
    rrgval.b
    cR
    cbs
    fvex
    eqeltri
    rabex
    fvmpt
    @9
    wn
    #
    @0
    c0
    @8
    cR
    crlreg
    fvprc
    @23
    @8
    @7
    vx
    c0
    crab
    #
    c0
    @23
    cB
    c0
    wceq
    @8
    @24
    wceq
    @23
    cB
    @20
    c0
    rrgval.b
    cR
    cbs
    fvprc
    syl5eq
    @7
    vx
    cB
    c0
    rabeq
    syl
    @7
    vx
    rab0
    syl6eq
    eqtr4d
    pm2.61i
    eqtri
end
