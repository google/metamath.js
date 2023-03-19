include "tgbtwncom.mm"
include "tgbtwnexch2.mm"

theorem tgbtwnexch
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
  assume tgbtwnexch.1: |- ( ph -> B e. ( A I C ) )
  assume tgbtwnexch.2: |- ( ph -> C e. ( A I D ) )


  assert |- ( ph -> B e. ( A I D ) )

  proof
    wph
    cD
    cB
    cA
    cP
    cG
    cI
    c.mi
    tkgeom.p
    tkgeom.d
    tkgeom.i
    tkgeom.g
    tgbtwnintr.4
    tgbtwnintr.2
    tgbtwnintr.1
    wph
    cD
    cC
    cB
    cA
    cP
    cG
    cI
    c.mi
    tkgeom.p
    tkgeom.d
    tkgeom.i
    tkgeom.g
    tgbtwnintr.4
    tgbtwnintr.3
    tgbtwnintr.2
    tgbtwnintr.1
    wph
    cA
    cC
    cD
    cP
    cG
    cI
    c.mi
    tkgeom.p
    tkgeom.d
    tkgeom.i
    tkgeom.g
    tgbtwnintr.1
    tgbtwnintr.3
    tgbtwnintr.4
    tgbtwnexch.2
    tgbtwncom
    wph
    cA
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
    tgbtwnintr.1
    tgbtwnintr.2
    tgbtwnintr.3
    tgbtwnexch.1
    tgbtwncom
    tgbtwnexch2
    tgbtwncom
end
