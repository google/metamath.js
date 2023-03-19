include "wo.mm"
include "wi.mm"
include "wn.mm"
include "wa.mm"
include "pm3.35.mm"
include "ord.mm"
include "expimpd.mm"

theorem ornld
  let wph: wff ph
  let wth: wff th
  let wta: wff ta


  assert |- ( ph -> ( ( ( ph -> ( th \/ ta ) ) /\ -. th ) -> ta ) )

  proof
    wph
    wph
    wth
    wta
    wo
    #
    wi
    #
    wth
    wn
    wta
    wph
    @1
    wa
    wth
    wta
    wph
    @0
    pm3.35
    ord
    expimpd
end
