include "wif.mm"
include "wb.mm"
include "wa.mm"
include "wi.mm"
include "wo.mm"
include "olc.mm"
include "pm3.2i.mm"
include "ifpidg.mm"
include "mpbiran2.mm"

theorem ifpid3g
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ch <-> if- ( ph , ps , ch ) ) <-> ( ( ( ph /\ ps ) -> ch ) /\ ( ( ph /\ ch ) -> ps ) ) )

  proof
    wch
    wph
    wps
    wch
    wif
    wb
    wph
    wps
    wa
    wch
    wi
    wph
    wch
    wa
    wps
    wi
    wa
    wch
    wph
    wch
    wo
    wi
    #
    @0
    wa
    @0
    @0
    wch
    wph
    olc
    #
    @1
    pm3.2i
    wph
    wps
    wch
    wch
    ifpidg
    mpbiran2
end
