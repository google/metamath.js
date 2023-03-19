include "cgsu.mm"
include "co.mm"
include "ctsu.mm"
include "wcel.mm"
include "csn.mm"
include "wceq.mm"
include "tsmsid.mm"
include "haustsms2.mm"
include "mpd.mm"

theorem haustsmsid
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cJ: class J
  let cV: class V
  let c.0: class .0.
  let vy: setvar y
  let vz: setvar z
  let vu: setvar u
  let vx: setvar x
  assume tsmsid.b: |- B = ( Base ` G )
  assume tsmsid.z: |- .0. = ( 0g ` G )
  assume tsmsid.1: |- ( ph -> G e. CMnd )
  assume tsmsid.2: |- ( ph -> G e. TopSp )
  assume tsmsid.a: |- ( ph -> A e. V )
  assume tsmsid.f: |- ( ph -> F : A --> B )
  assume tsmsid.w: |- ( ph -> F finSupp .0. )
  assume haustsmsid.j: |- J = ( TopOpen ` G )
  assume haustsmsid.h: |- ( ph -> J e. Haus )


  assert |- ( ph -> ( G tsums F ) = { ( G gsum F ) } )

  proof
    wph
    cG
    cF
    cgsu
    co
    #
    cG
    cF
    ctsu
    co
    #
    wcel
    @1
    @0
    csn
    wceq
    wph
    cA
    cB
    cF
    cG
    cV
    c.0
    tsmsid.b
    tsmsid.z
    tsmsid.1
    tsmsid.2
    tsmsid.a
    tsmsid.f
    tsmsid.w
    tsmsid
    wph
    cA
    cB
    cF
    cG
    cJ
    cV
    @0
    tsmsid.b
    tsmsid.1
    tsmsid.2
    tsmsid.a
    tsmsid.f
    haustsmsid.j
    haustsmsid.h
    haustsms2
    mpd
end
