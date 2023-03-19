include "wne.mm"
include "wa.mm"
include "wi.mm"
include "wceq.mm"
include "a1d.mm"
include "3exp2.mm"
include "imp4b.mm"
include "pm2.61dane.mm"
include "imp.mm"
include "pm2.61da2ne.mm"

theorem pm2.61da3ne
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  assume pm2.61da3ne.1: |- ( ( ph /\ A = B ) -> ps )
  assume pm2.61da3ne.2: |- ( ( ph /\ C = D ) -> ps )
  assume pm2.61da3ne.3: |- ( ( ph /\ E = F ) -> ps )
  assume pm2.61da3ne.4: |- ( ( ph /\ ( A =/= B /\ C =/= D /\ E =/= F ) ) -> ps )


  assert |- ( ph -> ps )

  proof
    wph
    wps
    cC
    cD
    cE
    cF
    pm2.61da3ne.2
    pm2.61da3ne.3
    wph
    cC
    cD
    wne
    #
    cE
    cF
    wne
    #
    wa
    #
    wps
    wph
    @2
    wps
    wi
    cA
    cB
    wph
    cA
    cB
    wceq
    wa
    wps
    @2
    pm2.61da3ne.1
    a1d
    wph
    cA
    cB
    wne
    #
    @0
    @1
    wps
    wph
    @3
    @0
    @1
    wps
    pm2.61da3ne.4
    3exp2
    imp4b
    pm2.61dane
    imp
    pm2.61da2ne
end
