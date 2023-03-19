include "cv.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cstrkg.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "simprr.mm"
include "axtgbtwnid.mm"
include "simprl.mm"
include "eqeltrd.mm"
include "axtgpasch.mm"
include "r19.29a.mm"

theorem tgbtwnintr
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cG: class G
  let cI: class I
  let c.mi: class .-
  let vx: setvar x
  assume tkgeom.p: |- P = ( Base ` G )
  assume tkgeom.d: |- .- = ( dist ` G )
  assume tkgeom.i: |- I = ( Itv ` G )
  assume tkgeom.g: |- ( ph -> G e. TarskiG )
  assume tgbtwnintr.1: |- ( ph -> A e. P )
  assume tgbtwnintr.2: |- ( ph -> B e. P )
  assume tgbtwnintr.3: |- ( ph -> C e. P )
  assume tgbtwnintr.4: |- ( ph -> D e. P )
  assume tgbtwnintr.5: |- ( ph -> A e. ( B I D ) )
  assume tgbtwnintr.6: |- ( ph -> B e. ( C I D ) )


  assert |- ( ph -> B e. ( A I C ) )

  proof
    wph
    vx
    cv
    #
    cA
    cC
    cI
    co
    #
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
    cB
    @1
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
    @1
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
    tgbtwnintr.2
    ad2antrr
    wph
    @5
    @4
    simplr
    @6
    @2
    @3
    simprr
    axtgbtwnid
    @6
    @2
    @3
    simprl
    eqeltrd
    wph
    cP
    cA
    cG
    cI
    c.mi
    cB
    cB
    cC
    cD
    vx
    tkgeom.p
    tkgeom.d
    tkgeom.i
    tkgeom.g
    tgbtwnintr.2
    tgbtwnintr.3
    tgbtwnintr.4
    tgbtwnintr.1
    tgbtwnintr.2
    tgbtwnintr.5
    tgbtwnintr.6
    axtgpasch
    r19.29a
end
