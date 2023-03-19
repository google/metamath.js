include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "wrex.mm"
include "crab.mm"
include "cvv.mm"
include "cmpt2.mm"
include "cnx.mm"
include "citv.mm"
include "cfv.mm"
include "cop.mm"
include "csts.mm"
include "clng.mm"
include "w3o.mm"
include "ttgval.mm"
include "simprd.mm"
include "3ad2ant1.mm"
include "wa.mm"
include "simprl.mm"
include "oveq2d.mm"
include "simprr.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "rexbidv.mm"
include "rabbidv.mm"
include "simp2.mm"
include "simp3.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "rabex.mm"
include "a1i.mm"
include "ovmpt2d.mm"

theorem ttgitvval
  let vz: setvar z
  let cP: class P
  let c.x: class .x.
  let vk: setvar k
  let cG: class G
  let cH: class H
  let cI: class I
  let c.mi: class .-
  let cV: class V
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let cZ: class Z
  assume ttgval.n: |- G = ( toTG ` H )
  assume ttgitvval.i: |- I = ( Itv ` G )
  assume ttgitvval.b: |- P = ( Base ` H )
  assume ttgitvval.m: |- .- = ( -g ` H )
  assume ttgitvval.s: |- .x. = ( .s ` H )

  disjoint k z
  disjoint .- k
  disjoint .- z
  disjoint .x. z
  disjoint H k
  disjoint H z
  disjoint P k
  disjoint P z
  disjoint V k
  disjoint V z
  disjoint X k
  disjoint X z
  disjoint Y k
  disjoint Y z
  disjoint k x
  disjoint k y
  disjoint x y
  disjoint x z
  disjoint .- x
  disjoint y z
  disjoint .- y
  disjoint .x. x
  disjoint .x. y
  disjoint H x
  disjoint H y
  disjoint P x
  disjoint P y
  disjoint V x
  disjoint V y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint Z k
  disjoint Z z
  assert |- ( ( H e. V /\ X e. P /\ Y e. P ) -> ( X I Y ) = { z e. P | E. k e. ( 0 [,] 1 ) ( z .- X ) = ( k .x. ( Y .- X ) ) } )

  proof
    cH
    cV
    wcel
    #
    cX
    cP
    wcel
    #
    cY
    cP
    wcel
    #
    w3a
    #
    vx
    vy
    cX
    cY
    cP
    cP
    vz
    cv
    #
    vx
    cv
    #
    c.mi
    co
    #
    vk
    cv
    #
    vy
    cv
    #
    @5
    c.mi
    co
    #
    c.x
    co
    #
    wceq
    #
    vk
    cc0
    c1
    cicc
    co
    #
    wrex
    #
    vz
    cP
    crab
    #
    @4
    cX
    c.mi
    co
    #
    @7
    cY
    cX
    c.mi
    co
    #
    c.x
    co
    #
    wceq
    #
    vk
    @12
    wrex
    #
    vz
    cP
    crab
    #
    cI
    cvv
    @0
    @1
    cI
    vx
    vy
    cP
    cP
    @14
    cmpt2
    #
    wceq
    #
    @2
    @0
    cG
    cH
    cnx
    citv
    cfv
    @21
    cop
    csts
    co
    cnx
    clng
    cfv
    vx
    vy
    cP
    cP
    @4
    @5
    @8
    cI
    co
    wcel
    @5
    @4
    @8
    cI
    co
    wcel
    @8
    @5
    @4
    cI
    co
    wcel
    w3o
    vz
    cP
    crab
    cmpt2
    cop
    csts
    co
    wceq
    @22
    vx
    vy
    vz
    cP
    c.x
    vk
    cG
    cH
    cI
    c.mi
    cV
    ttgval.n
    ttgitvval.b
    ttgitvval.m
    ttgitvval.s
    ttgitvval.i
    ttgval
    simprd
    3ad2ant1
    @3
    @5
    cX
    wceq
    #
    @8
    cY
    wceq
    #
    wa
    wa
    #
    @13
    @19
    vz
    cP
    @25
    @11
    @18
    vk
    @12
    @25
    @6
    @15
    @10
    @17
    @25
    @5
    cX
    @4
    c.mi
    @3
    @23
    @24
    simprl
    #
    oveq2d
    @25
    @9
    @16
    @7
    c.x
    @25
    @8
    cY
    @5
    cX
    c.mi
    @3
    @23
    @24
    simprr
    @26
    oveq12d
    oveq2d
    eqeq12d
    rexbidv
    rabbidv
    @0
    @1
    @2
    simp2
    @0
    @1
    @2
    simp3
    @20
    cvv
    wcel
    @3
    @19
    vz
    cP
    cP
    cH
    cbs
    cfv
    cvv
    ttgitvval.b
    cH
    cbs
    fvex
    eqeltri
    rabex
    a1i
    ovmpt2d
end
