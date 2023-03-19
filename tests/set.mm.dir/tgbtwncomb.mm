include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cstrkg.mm"
include "adantr.mm"
include "simpr.mm"
include "tgbtwncom.mm"
include "impbida.mm"

theorem tgbtwncomb
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
  assume tgbtwncomb.3: |- ( ph -> C e. P )


  assert |- ( ph -> ( B e. ( A I C ) <-> B e. ( C I A ) ) )

  proof
    wph
    cB
    cA
    cC
    cI
    co
    wcel
    #
    cB
    cC
    cA
    cI
    co
    wcel
    #
    wph
    @0
    wa
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
    wph
    cG
    cstrkg
    wcel
    #
    @0
    tkgeom.g
    adantr
    wph
    cA
    cP
    wcel
    #
    @0
    tgbtwntriv2.1
    adantr
    wph
    cB
    cP
    wcel
    #
    @0
    tgbtwntriv2.2
    adantr
    wph
    cC
    cP
    wcel
    #
    @0
    tgbtwncomb.3
    adantr
    wph
    @0
    simpr
    tgbtwncom
    wph
    @1
    wa
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
    wph
    @2
    @1
    tkgeom.g
    adantr
    wph
    @5
    @1
    tgbtwncomb.3
    adantr
    wph
    @4
    @1
    tgbtwntriv2.2
    adantr
    wph
    @3
    @1
    tgbtwntriv2.1
    adantr
    wph
    @1
    simpr
    tgbtwncom
    impbida
end
