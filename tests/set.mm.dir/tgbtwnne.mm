include "wceq.mm"
include "wa.mm"
include "cstrkg.mm"
include "wcel.mm"
include "adantr.mm"
include "co.mm"
include "simpr.mm"
include "oveq2d.mm"
include "eleqtrrd.mm"
include "axtgbtwnid.mm"
include "eqcomd.mm"
include "wne.mm"
include "neneqd.mm"
include "pm2.65da.mm"
include "neqned.mm"

theorem tgbtwnne
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
  assume tgbtwnne.1: |- ( ph -> B e. ( A I C ) )
  assume tgbtwnne.2: |- ( ph -> B =/= A )


  assert |- ( ph -> A =/= C )

  proof
    wph
    cA
    cC
    wph
    cA
    cC
    wceq
    #
    cB
    cA
    wceq
    wph
    @0
    wa
    #
    cA
    cB
    @1
    cP
    cG
    cI
    c.mi
    cA
    cB
    tkgeom.p
    tkgeom.d
    tkgeom.i
    wph
    cG
    cstrkg
    wcel
    @0
    tkgeom.g
    adantr
    wph
    cA
    cP
    wcel
    @0
    tgbtwntriv2.1
    adantr
    wph
    cB
    cP
    wcel
    @0
    tgbtwntriv2.2
    adantr
    @1
    cB
    cA
    cC
    cI
    co
    #
    cA
    cA
    cI
    co
    wph
    cB
    @2
    wcel
    @0
    tgbtwnne.1
    adantr
    @1
    cA
    cC
    cA
    cI
    wph
    @0
    simpr
    oveq2d
    eleqtrrd
    axtgbtwnid
    eqcomd
    @1
    cB
    cA
    wph
    cB
    cA
    wne
    @0
    tgbtwnne.2
    adantr
    neneqd
    pm2.65da
    neqned
end
