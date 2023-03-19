include "wi.mm"
include "wceq.mm"
include "syl5ibr.mm"
include "wne.mm"
include "expcom.mm"
include "pm2.61ine.mm"

theorem pm2.61ne
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let cA: class A
  let cB: class B
  assume pm2.61ne.1: |- ( A = B -> ( ps <-> ch ) )
  assume pm2.61ne.2: |- ( ( ph /\ A =/= B ) -> ps )
  assume pm2.61ne.3: |- ( ph -> ch )


  assert |- ( ph -> ps )

  proof
    wph
    wps
    wi
    cA
    cB
    wph
    wps
    cA
    cB
    wceq
    wch
    pm2.61ne.3
    pm2.61ne.1
    syl5ibr
    wph
    cA
    cB
    wne
    wps
    pm2.61ne.2
    expcom
    pm2.61ine
end
