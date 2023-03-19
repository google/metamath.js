include "cv.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "cstrkg.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "simprl.mm"
include "axtgbtwnid.mm"
include "simprr.mm"
include "eqtr4d.mm"
include "axtgpasch.mm"
include "r19.29a.mm"

theorem tgbtwnswapid
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cG: class G
  let cI: class I
  let c.mi: class .-
  let vx: setvar x
  let cD: class D
  assume tkgeom.p: |- P = ( Base ` G )
  assume tkgeom.d: |- .- = ( dist ` G )
  assume tkgeom.i: |- I = ( Itv ` G )
  assume tkgeom.g: |- ( ph -> G e. TarskiG )
  assume tgbtwnswapid.1: |- ( ph -> A e. P )
  assume tgbtwnswapid.2: |- ( ph -> B e. P )
  assume tgbtwnswapid.3: |- ( ph -> C e. P )
  assume tgbtwnswapid.4: |- ( ph -> A e. ( B I C ) )
  assume tgbtwnswapid.5: |- ( ph -> B e. ( A I C ) )


  assert |- ( ph -> A = B )

  proof
    wph
    vx
    cv
    #
    cA
    cA
    cI
    co
    wcel
    #
    @0
    cB
    cB
    cI
    co
    wcel
    #
    wa
    #
    cA
    cB
    wceq
    vx
    cP
    wph
    @0
    cP
    wcel
    #
    wa
    #
    @3
    wa
    #
    cA
    @0
    cB
    @6
    cP
    cG
    cI
    c.mi
    cA
    @0
    tkgeom.p
    tkgeom.d
    tkgeom.i
    wph
    cG
    cstrkg
    wcel
    @4
    @3
    tkgeom.g
    ad2antrr
    #
    wph
    cA
    cP
    wcel
    @4
    @3
    tgbtwnswapid.1
    ad2antrr
    wph
    @4
    @3
    simplr
    #
    @5
    @1
    @2
    simprl
    axtgbtwnid
    @6
    cP
    cG
    cI
    c.mi
    cB
    @0
    tkgeom.p
    tkgeom.d
    tkgeom.i
    @7
    wph
    cB
    cP
    wcel
    @4
    @3
    tgbtwnswapid.2
    ad2antrr
    @8
    @5
    @1
    @2
    simprr
    axtgbtwnid
    eqtr4d
    wph
    cP
    cA
    cG
    cI
    c.mi
    cB
    cB
    cA
    cC
    vx
    tkgeom.p
    tkgeom.d
    tkgeom.i
    tkgeom.g
    tgbtwnswapid.2
    tgbtwnswapid.1
    tgbtwnswapid.3
    tgbtwnswapid.1
    tgbtwnswapid.2
    tgbtwnswapid.4
    tgbtwnswapid.5
    axtgpasch
    r19.29a
end
