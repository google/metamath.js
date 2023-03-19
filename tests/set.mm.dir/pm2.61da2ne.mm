include "wne.mm"
include "wa.mm"
include "wceq.mm"
include "adantlr.mm"
include "anassrs.mm"
include "pm2.61dane.mm"

theorem pm2.61da2ne
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume pm2.61da2ne.1: |- ( ( ph /\ A = B ) -> ps )
  assume pm2.61da2ne.2: |- ( ( ph /\ C = D ) -> ps )
  assume pm2.61da2ne.3: |- ( ( ph /\ ( A =/= B /\ C =/= D ) ) -> ps )


  assert |- ( ph -> ps )

  proof
    wph
    wps
    cA
    cB
    pm2.61da2ne.1
    wph
    cA
    cB
    wne
    #
    wa
    wps
    cC
    cD
    wph
    cC
    cD
    wceq
    wps
    @0
    pm2.61da2ne.2
    adantlr
    wph
    @0
    cC
    cD
    wne
    wps
    pm2.61da2ne.3
    anassrs
    pm2.61dane
    pm2.61dane
end
