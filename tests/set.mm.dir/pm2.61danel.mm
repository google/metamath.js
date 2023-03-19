include "wcel.mm"
include "wn.mm"
include "wnel.mm"
include "df-nel.mm"
include "sylan2br.mm"
include "pm2.61dan.mm"

theorem pm2.61danel
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  assume pm2.61danel.1: |- ( ( ph /\ A e. B ) -> ps )
  assume pm2.61danel.2: |- ( ( ph /\ A e/ B ) -> ps )


  assert |- ( ph -> ps )

  proof
    wph
    cA
    cB
    wcel
    #
    wps
    pm2.61danel.1
    @0
    wn
    wph
    cA
    cB
    wnel
    wps
    cA
    cB
    df-nel
    pm2.61danel.2
    sylan2br
    pm2.61dan
end
