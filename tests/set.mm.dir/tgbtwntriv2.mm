include "cv.mm"
include "co.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "simprl.mm"
include "cstrkg.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "simpr.mm"
include "axtgcgrid.mm"
include "adantrl.mm"
include "oveq2d.mm"
include "eleqtrrd.mm"
include "axtgsegcon.mm"
include "r19.29a.mm"

theorem tgbtwntriv2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let cG: class G
  let cI: class I
  let c.mi: class .-
  let vx: setvar x
  let cC: class C
  let cD: class D
  assume tkgeom.p: |- P = ( Base ` G )
  assume tkgeom.d: |- .- = ( dist ` G )
  assume tkgeom.i: |- I = ( Itv ` G )
  assume tkgeom.g: |- ( ph -> G e. TarskiG )
  assume tgbtwntriv2.1: |- ( ph -> A e. P )
  assume tgbtwntriv2.2: |- ( ph -> B e. P )


  assert |- ( ph -> B e. ( A I B ) )

  proof
    wph
    cB
    cA
    vx
    cv
    #
    cI
    co
    #
    wcel
    #
    cB
    @0
    c.mi
    co
    cB
    cB
    c.mi
    co
    wceq
    #
    wa
    #
    cB
    cA
    cB
    cI
    co
    #
    wcel
    vx
    cP
    wph
    @0
    cP
    wcel
    #
    wa
    #
    @4
    wa
    #
    cB
    @1
    @5
    @7
    @2
    @3
    simprl
    @8
    cB
    @0
    cA
    cI
    @7
    @3
    cB
    @0
    wceq
    @2
    @7
    @3
    wa
    cP
    cG
    cI
    c.mi
    cB
    @0
    cB
    tkgeom.p
    tkgeom.d
    tkgeom.i
    wph
    cG
    cstrkg
    wcel
    @6
    @3
    tkgeom.g
    ad2antrr
    wph
    cB
    cP
    wcel
    @6
    @3
    tgbtwntriv2.2
    ad2antrr
    #
    wph
    @6
    @3
    simplr
    @9
    @7
    @3
    simpr
    axtgcgrid
    adantrl
    oveq2d
    eleqtrrd
    wph
    vx
    cB
    cB
    cP
    cG
    cI
    c.mi
    cA
    cB
    tkgeom.p
    tkgeom.d
    tkgeom.i
    tkgeom.g
    tgbtwntriv2.1
    tgbtwntriv2.2
    tgbtwntriv2.2
    tgbtwntriv2.2
    axtgsegcon
    r19.29a
end
