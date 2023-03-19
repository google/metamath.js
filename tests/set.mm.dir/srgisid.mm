include "co.mm"
include "cv.mm"
include "wceq.mm"
include "wral.mm"
include "ralrimiva.mm"
include "csrg.mm"
include "wcel.mm"
include "wi.mm"
include "srg0cl.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "rspcv.mm"
include "3syl.mm"
include "mpd.mm"
include "srgrz.mm"
include "syl2anc.mm"
include "eqtr3d.mm"

theorem srgisid
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let c.0: class .0.
  let cZ: class Z
  let vy: setvar y
  let vz: setvar z
  let cX: class X
  assume srgz.b: |- B = ( Base ` R )
  assume srgz.t: |- .x. = ( .r ` R )
  assume srgz.z: |- .0. = ( 0g ` R )
  assume srgisid.1: |- ( ph -> R e. SRing )
  assume srgisid.2: |- ( ph -> Z e. B )
  assume srgisid.3: |- ( ( ph /\ x e. B ) -> ( Z .x. x ) = Z )

  disjoint B x
  disjoint R x
  disjoint .x. x
  disjoint .0. x
  disjoint Z x
  disjoint ph x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint R y
  disjoint R z
  disjoint X x
  disjoint .x. y
  disjoint .x. z
  disjoint .0. y
  disjoint .0. z
  assert |- ( ph -> Z = .0. )

  proof
    wph
    cZ
    c.0
    c.x
    co
    #
    cZ
    c.0
    wph
    cZ
    vx
    cv
    #
    c.x
    co
    #
    cZ
    wceq
    #
    vx
    cB
    wral
    #
    @0
    cZ
    wceq
    #
    wph
    @3
    vx
    cB
    srgisid.3
    ralrimiva
    wph
    cR
    csrg
    wcel
    #
    c.0
    cB
    wcel
    @4
    @5
    wi
    srgisid.1
    cB
    cR
    c.0
    srgz.b
    srgz.z
    srg0cl
    @3
    @5
    vx
    c.0
    cB
    @1
    c.0
    wceq
    @2
    @0
    cZ
    @1
    c.0
    cZ
    c.x
    oveq2
    eqeq1d
    rspcv
    3syl
    mpd
    wph
    @6
    cZ
    cB
    wcel
    @0
    c.0
    wceq
    srgisid.1
    srgisid.2
    cB
    cR
    c.x
    cZ
    c.0
    srgz.b
    srgz.t
    srgz.z
    srgrz
    syl2anc
    eqtr3d
end
