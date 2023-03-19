include "tgbtwntriv2.mm"
include "tgbtwncom.mm"

theorem tgbtwntriv1
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


  assert |- ( ph -> A e. ( A I B ) )

  proof
    wph
    cB
    cA
    cA
    cP
    cG
    cI
    c.mi
    tkgeom.p
    tkgeom.d
    tkgeom.i
    tkgeom.g
    tgbtwntriv2.2
    tgbtwntriv2.1
    tgbtwntriv2.1
    wph
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
    tgbtwntriv2.2
    tgbtwntriv2.1
    tgbtwntriv2
    tgbtwncom
end
