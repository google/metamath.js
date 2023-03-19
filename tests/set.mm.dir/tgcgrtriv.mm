include "cv.mm"
include "co.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "cstrkg.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "simprr.mm"
include "axtgcgrid.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "axtgsegcon.mm"
include "r19.29a.mm"

theorem tgcgrtriv
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let cG: class G
  let cI: class I
  let c.mi: class .-
  let vx: setvar x
  assume tkgeom.p: |- P = ( Base ` G )
  assume tkgeom.d: |- .- = ( dist ` G )
  assume tkgeom.i: |- I = ( Itv ` G )
  assume tkgeom.g: |- ( ph -> G e. TarskiG )
  assume tgcgrtriv.1: |- ( ph -> A e. P )
  assume tgcgrtriv.2: |- ( ph -> B e. P )


  assert |- ( ph -> ( A .- A ) = ( B .- B ) )

  proof
    wph
    cA
    cB
    vx
    cv
    #
    cI
    co
    wcel
    #
    cA
    @0
    c.mi
    co
    #
    cB
    cB
    c.mi
    co
    #
    wceq
    #
    wa
    #
    cA
    cA
    c.mi
    co
    #
    @3
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
    @5
    wa
    #
    @6
    @2
    @3
    @9
    cA
    @0
    cA
    c.mi
    @9
    cP
    cG
    cI
    c.mi
    cA
    @0
    cB
    tkgeom.p
    tkgeom.d
    tkgeom.i
    wph
    cG
    cstrkg
    wcel
    @7
    @5
    tkgeom.g
    ad2antrr
    wph
    cA
    cP
    wcel
    @7
    @5
    tgcgrtriv.1
    ad2antrr
    wph
    @7
    @5
    simplr
    wph
    cB
    cP
    wcel
    @7
    @5
    tgcgrtriv.2
    ad2antrr
    @8
    @1
    @4
    simprr
    #
    axtgcgrid
    oveq2d
    @10
    eqtrd
    wph
    vx
    cB
    cB
    cP
    cG
    cI
    c.mi
    cB
    cA
    tkgeom.p
    tkgeom.d
    tkgeom.i
    tkgeom.g
    tgcgrtriv.2
    tgcgrtriv.1
    tgcgrtriv.2
    tgcgrtriv.2
    axtgsegcon
    r19.29a
end
