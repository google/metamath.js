include "chomf.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "cmpt2.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "cbs.mm"
include "chom.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "oveqd.mm"
include "mpt2eq123dv.mm"
include "df-homf.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mpt2ex.mm"
include "fvmpt.mm"
include "wn.mm"
include "c0.mm"
include "mpt20.mm"
include "eqcomi.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "mpt2eq12.mm"
include "syl2anc.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"
include "eqtri.mm"

theorem homffval
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let cF: class F
  let cH: class H
  let vc: setvar c
  let wph: wff ph
  let cX: class X
  let cY: class Y
  assume homffval.f: |- F = ( Homf ` C )
  assume homffval.b: |- B = ( Base ` C )
  assume homffval.h: |- H = ( Hom ` C )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint H x
  disjoint H y
  disjoint c x
  disjoint c y
  disjoint B c
  disjoint C c
  disjoint H c
  disjoint ph x
  disjoint ph y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  assert |- F = ( x e. B , y e. B |-> ( x H y ) )

  proof
    cF
    cC
    chomf
    cfv
    #
    vx
    vy
    cB
    cB
    vx
    cv
    #
    vy
    cv
    #
    cH
    co
    #
    cmpt2
    #
    homffval.f
    cC
    cvv
    wcel
    #
    @0
    @4
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
    @7
    @1
    @2
    @6
    chom
    cfv
    #
    co
    #
    cmpt2
    @4
    cvv
    chomf
    @6
    cC
    wceq
    #
    vx
    vy
    @7
    @7
    @9
    cB
    cB
    @3
    @10
    @7
    cC
    cbs
    cfv
    #
    cB
    @6
    cC
    cbs
    fveq2
    homffval.b
    syl6eqr
    #
    @12
    @10
    @8
    cH
    @1
    @2
    @10
    @8
    cC
    chom
    cfv
    cH
    @6
    cC
    chom
    fveq2
    homffval.h
    syl6eqr
    oveqd
    mpt2eq123dv
    vx
    vy
    vc
    df-homf
    vx
    vy
    cB
    cB
    @3
    cB
    @11
    cvv
    homffval.b
    cC
    cbs
    fvex
    eqeltri
    #
    @13
    mpt2ex
    fvmpt
    @5
    wn
    #
    c0
    vx
    vy
    c0
    c0
    @3
    cmpt2
    #
    @0
    @4
    @15
    c0
    vx
    vy
    c0
    @3
    mpt20
    eqcomi
    cC
    chomf
    fvprc
    @14
    cB
    c0
    wceq
    #
    @16
    @4
    @15
    wceq
    @14
    cB
    @11
    c0
    homffval.b
    cC
    cbs
    fvprc
    syl5eq
    #
    @17
    vx
    vy
    cB
    cB
    c0
    c0
    @3
    mpt2eq12
    syl2anc
    3eqtr4a
    pm2.61i
    eqtri
end
