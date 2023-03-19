include "crng.mm"
include "wcel.mm"
include "cabl.mm"
include "cgrp.mm"
include "rngabl.mm"
include "ablgrp.mm"
include "3syl.mm"
include "isghmd.mm"
include "isrnghm2d.mm"

theorem isrnghmd
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
  let cF: class F
  let vk: setvar k
  assume isrnghmd.b: |- B = ( Base ` R )
  assume isrnghmd.t: |- .x. = ( .r ` R )
  assume isrnghmd.u: |- .X. = ( .r ` S )
  assume isrnghmd.r: |- ( ph -> R e. Rng )
  assume isrnghmd.s: |- ( ph -> S e. Rng )
  assume isrnghmd.ht: |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> ( F ` ( x .x. y ) ) = ( ( F ` x ) .X. ( F ` y ) ) )
  assume isrnghmd.c: |- C = ( Base ` S )
  assume isrnghmd.p: |- .+ = ( +g ` R )
  assume isrnghmd.q: |- .+^ = ( +g ` S )
  assume isrnghmd.f: |- ( ph -> F : B --> C )
  assume isrnghmd.hp: |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> ( F ` ( x .+ y ) ) = ( ( F ` x ) .+^ ( F ` y ) ) )

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
  disjoint k x
  assert |- ( ph -> F e. ( R RngHomo S ) )

  proof
    wph
    vx
    vy
    cB
    cR
    cS
    c.x
    c.xp
    cF
    isrnghmd.b
    isrnghmd.t
    isrnghmd.u
    isrnghmd.r
    isrnghmd.s
    isrnghmd.ht
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
    isrnghmd.b
    isrnghmd.c
    isrnghmd.p
    isrnghmd.q
    wph
    cR
    crng
    wcel
    cR
    cabl
    wcel
    cR
    cgrp
    wcel
    isrnghmd.r
    cR
    rngabl
    cR
    ablgrp
    3syl
    wph
    cS
    crng
    wcel
    cS
    cabl
    wcel
    cS
    cgrp
    wcel
    isrnghmd.s
    cS
    rngabl
    cS
    ablgrp
    3syl
    isrnghmd.f
    isrnghmd.hp
    isghmd
    isrnghm2d
end
