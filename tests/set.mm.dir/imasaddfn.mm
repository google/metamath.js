include "imasplusg.mm"
include "imasaddfnlem.mm"

theorem imasaddfn
  let wph: wff ph
  let cB: class B
  let cR: class R
  let c.xb: class .xb
  let c.x: class .x.
  let cU: class U
  let cF: class F
  let cV: class V
  let cZ: class Z
  let vq: setvar q
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let cX: class X
  let vx: setvar x
  let cY: class Y
  assume imasaddf.f: |- ( ph -> F : V -onto-> B )
  assume imasaddf.e: |- ( ( ph /\ ( a e. V /\ b e. V ) /\ ( p e. V /\ q e. V ) ) -> ( ( ( F ` a ) = ( F ` p ) /\ ( F ` b ) = ( F ` q ) ) -> ( F ` ( a .x. b ) ) = ( F ` ( p .x. q ) ) ) )
  assume imasaddf.u: |- ( ph -> U = ( F "s R ) )
  assume imasaddf.v: |- ( ph -> V = ( Base ` R ) )
  assume imasaddf.r: |- ( ph -> R e. Z )
  assume imasaddf.p: |- .x. = ( +g ` R )
  assume imasaddf.a: |- .xb = ( +g ` U )

  disjoint p q
  disjoint B p
  disjoint B q
  disjoint R p
  disjoint R q
  disjoint a b
  disjoint a p
  disjoint a q
  disjoint V a
  disjoint b p
  disjoint b q
  disjoint V b
  disjoint V p
  disjoint V q
  disjoint .x. p
  disjoint .x. q
  disjoint F a
  disjoint F b
  disjoint F p
  disjoint F q
  disjoint a ph
  disjoint b ph
  disjoint p ph
  disjoint ph q
  disjoint .xb a
  disjoint .xb b
  disjoint .xb p
  disjoint .xb q
  disjoint a w
  disjoint a y
  disjoint a z
  disjoint b w
  disjoint b y
  disjoint b z
  disjoint p w
  disjoint p y
  disjoint p z
  disjoint q w
  disjoint q y
  disjoint q z
  disjoint w y
  disjoint w z
  disjoint V w
  disjoint y z
  disjoint V y
  disjoint V z
  disjoint .x. w
  disjoint X p
  disjoint a x
  disjoint b x
  disjoint p x
  disjoint q x
  disjoint w x
  disjoint F w
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint ph w
  disjoint .xb w
  disjoint .xb x
  disjoint .xb y
  disjoint .xb z
  disjoint Y p
  disjoint Y q
  assert |- ( ph -> .xb Fn ( B X. B ) )

  proof
    wph
    cB
    c.xb
    c.x
    cF
    cV
    vq
    vp
    va
    vb
    imasaddf.f
    imasaddf.e
    wph
    cB
    c.x
    c.xb
    cR
    cU
    cF
    cV
    cZ
    vq
    vp
    imasaddf.u
    imasaddf.v
    imasaddf.f
    imasaddf.r
    imasaddf.p
    imasaddf.a
    imasplusg
    imasaddfnlem
end
