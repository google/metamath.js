include "crg.mm"
include "wcel.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "syl.mm"
include "isghmd.mm"
include "isrhm2d.mm"

theorem isrhmd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let c.pl: class .+
  let c.pd: class .+^
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let c.xp: class .X.
  let c.1: class .1.
  let cF: class F
  let cN: class N
  assume isrhmd.b: |- B = ( Base ` R )
  assume isrhmd.o: |- .1. = ( 1r ` R )
  assume isrhmd.n: |- N = ( 1r ` S )
  assume isrhmd.t: |- .x. = ( .r ` R )
  assume isrhmd.u: |- .X. = ( .r ` S )
  assume isrhmd.r: |- ( ph -> R e. Ring )
  assume isrhmd.s: |- ( ph -> S e. Ring )
  assume isrhmd.ho: |- ( ph -> ( F ` .1. ) = N )
  assume isrhmd.ht: |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> ( F ` ( x .x. y ) ) = ( ( F ` x ) .X. ( F ` y ) ) )
  assume isrhmd.c: |- C = ( Base ` S )
  assume isrhmd.p: |- .+ = ( +g ` R )
  assume isrhmd.q: |- .+^ = ( +g ` S )
  assume isrhmd.f: |- ( ph -> F : B --> C )
  assume isrhmd.hp: |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> ( F ` ( x .+ y ) ) = ( ( F ` x ) .+^ ( F ` y ) ) )

  disjoint ph x
  disjoint ph y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint F x
  disjoint F y
  disjoint .+ x
  disjoint .+ y
  disjoint .+^ x
  disjoint .+^ y
  disjoint R x
  disjoint R y
  disjoint S x
  disjoint S y
  assert |- ( ph -> F e. ( R RingHom S ) )

  proof
    wph
    vx
    vy
    cB
    cR
    cS
    c.x
    c.xp
    c.1
    cF
    cN
    isrhmd.b
    isrhmd.o
    isrhmd.n
    isrhmd.t
    isrhmd.u
    isrhmd.r
    isrhmd.s
    isrhmd.ho
    isrhmd.ht
    wph
    vx
    vy
    c.pl
    c.pd
    cR
    cS
    cF
    cB
    cC
    isrhmd.b
    isrhmd.c
    isrhmd.p
    isrhmd.q
    wph
    cR
    crg
    wcel
    cR
    cgrp
    wcel
    isrhmd.r
    cR
    ringgrp
    syl
    wph
    cS
    crg
    wcel
    cS
    cgrp
    wcel
    isrhmd.s
    cS
    ringgrp
    syl
    isrhmd.f
    isrhmd.hp
    isghmd
    isrhm2d
end
