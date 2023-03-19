include "co.mm"
include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "wrex.mm"
include "wa.mm"
include "crab.mm"
include "ttgitvval.mm"
include "syl3anc.mm"
include "eleq2d.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "rexbidv.mm"
include "elrab.mm"
include "syl6bb.mm"
include "biantrurd.mm"
include "bitr4d.mm"

theorem ttgelitv
  let wph: wff ph
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
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume ttgval.n: |- G = ( toTG ` H )
  assume ttgitvval.i: |- I = ( Itv ` G )
  assume ttgitvval.b: |- P = ( Base ` H )
  assume ttgitvval.m: |- .- = ( -g ` H )
  assume ttgitvval.s: |- .x. = ( .s ` H )
  assume ttgelitv.x: |- ( ph -> X e. P )
  assume ttgelitv.y: |- ( ph -> Y e. P )
  assume ttgelitv.h: |- ( ph -> H e. V )
  assume ttgelitv.z: |- ( ph -> Z e. P )

  disjoint .- k
  disjoint H k
  disjoint P k
  disjoint V k
  disjoint X k
  disjoint Y k
  disjoint Z k
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint x y
  disjoint x z
  disjoint .- x
  disjoint y z
  disjoint .- y
  disjoint .- z
  disjoint .x. x
  disjoint .x. y
  disjoint .x. z
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint V x
  disjoint V y
  disjoint V z
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint Y x
  disjoint Y y
  disjoint Y z
  disjoint Z z
  assert |- ( ph -> ( Z e. ( X I Y ) <-> E. k e. ( 0 [,] 1 ) ( Z .- X ) = ( k .x. ( Y .- X ) ) ) )

  proof
    wph
    cZ
    cX
    cY
    cI
    co
    #
    wcel
    #
    cZ
    cP
    wcel
    #
    cZ
    cX
    c.mi
    co
    #
    vk
    cv
    cY
    cX
    c.mi
    co
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
    wa
    #
    @7
    wph
    @1
    cZ
    vz
    cv
    #
    cX
    c.mi
    co
    #
    @4
    wceq
    #
    vk
    @6
    wrex
    #
    vz
    cP
    crab
    #
    wcel
    @8
    wph
    @0
    @13
    cZ
    wph
    cH
    cV
    wcel
    cX
    cP
    wcel
    cY
    cP
    wcel
    @0
    @13
    wceq
    ttgelitv.h
    ttgelitv.x
    ttgelitv.y
    vz
    cP
    c.x
    vk
    cG
    cH
    cI
    c.mi
    cV
    cX
    cY
    ttgval.n
    ttgitvval.i
    ttgitvval.b
    ttgitvval.m
    ttgitvval.s
    ttgitvval
    syl3anc
    eleq2d
    @12
    @7
    vz
    cZ
    cP
    @9
    cZ
    wceq
    #
    @11
    @5
    vk
    @6
    @14
    @10
    @3
    @4
    @9
    cZ
    cX
    c.mi
    oveq1
    eqeq1d
    rexbidv
    elrab
    syl6bb
    wph
    @2
    @7
    ttgelitv.z
    biantrurd
    bitr4d
end
