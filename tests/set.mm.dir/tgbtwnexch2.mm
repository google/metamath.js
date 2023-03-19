include "co.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "simpr.mm"
include "adantr.mm"
include "eqeltrrd.mm"
include "wne.mm"
include "cstrkg.mm"
include "tgbtwnintr.mm"
include "tgbtwncom.mm"
include "tgbtwnouttr2.mm"
include "pm2.61dane.mm"

theorem tgbtwnexch2
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
  assume tgbtwnexch2.1: |- ( ph -> B e. ( A I D ) )
  assume tgbtwnexch2.2: |- ( ph -> C e. ( B I D ) )


  assert |- ( ph -> C e. ( A I D ) )

  proof
    wph
    cC
    cA
    cD
    cI
    co
    #
    wcel
    cB
    cC
    wph
    cB
    cC
    wceq
    #
    wa
    cB
    cC
    @0
    wph
    @1
    simpr
    wph
    cB
    @0
    wcel
    #
    @1
    tgbtwnexch2.1
    adantr
    eqeltrrd
    wph
    cB
    cC
    wne
    #
    wa
    #
    cA
    cB
    cC
    cD
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
    @3
    tkgeom.g
    adantr
    #
    wph
    cA
    cP
    wcel
    @3
    tgbtwnintr.1
    adantr
    #
    wph
    cB
    cP
    wcel
    @3
    tgbtwnintr.2
    adantr
    #
    wph
    cC
    cP
    wcel
    @3
    tgbtwnintr.3
    adantr
    #
    wph
    cD
    cP
    wcel
    @3
    tgbtwnintr.4
    adantr
    #
    wph
    @3
    simpr
    @4
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
    @5
    @8
    @7
    @6
    @4
    cC
    cB
    cA
    cD
    cP
    cG
    cI
    c.mi
    tkgeom.p
    tkgeom.d
    tkgeom.i
    @5
    @8
    @7
    @6
    @9
    wph
    cC
    cB
    cD
    cI
    co
    wcel
    @3
    tgbtwnexch2.2
    adantr
    #
    wph
    @2
    @3
    tgbtwnexch2.1
    adantr
    tgbtwnintr
    tgbtwncom
    @10
    tgbtwnouttr2
    pm2.61dane
end
