include "wi.mm"
include "wn.mm"
include "ax-1.mm"
include "con3i.mm"
include "pm2.21d.mm"
include "orri.mm"

theorem pm5.14
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph -> ps ) \/ ( ps -> ch ) )

  proof
    wph
    wps
    wi
    #
    wps
    wch
    wi
    @0
    wn
    wps
    wch
    wps
    @0
    wps
    wph
    ax-1
    con3i
    pm2.21d
    orri
end
