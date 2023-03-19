include "cv.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cstrkg.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "simprl.mm"
include "axtgbtwnid.mm"
include "simprr.mm"
include "eqeltrd.mm"
include "tgbtwntriv2.mm"
include "axtgpasch.mm"
include "r19.29a.mm"

theorem tgbtwncom
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
  assume tgbtwntriv2.1: |- ( ph -> A e. P )
  assume tgbtwntriv2.2: |- ( ph -> B e. P )
  assume tgbtwncom.3: |- ( ph -> C e. P )
  assume tgbtwncom.4: |- ( ph -> B e. ( A I C ) )


  assert |- ( ph -> B e. ( C I A ) )

  proof
    wph
    vx
    cv
    #
    cB
    cB
    cI
    co
    wcel
    #
    @0
    cC
    cA
    cI
    co
    #
    wcel
    #
    wa
    #
    cB
    @2
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
    @0
    @2
    @7
    cP
    cG
    cI
    c.mi
    cB
    @0
    tkgeom.p
    tkgeom.d
    tkgeom.i
    wph
    cG
    cstrkg
    wcel
    @5
    @4
    tkgeom.g
    ad2antrr
    wph
    cB
    cP
    wcel
    @5
    @4
    tgbtwntriv2.2
    ad2antrr
    wph
    @5
    @4
    simplr
    @6
    @1
    @3
    simprl
    axtgbtwnid
    @6
    @1
    @3
    simprr
    eqeltrd
    wph
    cP
    cB
    cG
    cI
    c.mi
    cC
    cA
    cB
    cC
    vx
    tkgeom.p
    tkgeom.d
    tkgeom.i
    tkgeom.g
    tgbtwntriv2.1
    tgbtwntriv2.2
    tgbtwncom.3
    tgbtwntriv2.2
    tgbtwncom.3
    tgbtwncom.4
    wph
    cB
    cC
    cP
    cG
    cI
    c.mi
    tkgeom.p
    tkgeom.d
    tkgeom.i
    tkgeom.g
    tgbtwntriv2.2
    tgbtwncom.3
    tgbtwntriv2
    axtgpasch
    r19.29a
end
