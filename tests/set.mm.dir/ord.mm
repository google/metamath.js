include "wo.mm"
include "wn.mm"
include "wi.mm"
include "df-or.mm"
include "sylib.mm"

theorem ord
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume ord.1: |- ( ph -> ( ps \/ ch ) )


  assert |- ( ph -> ( -. ps -> ch ) )

  proof
    wph
    wps
    wch
    wo
    wps
    wn
    wch
    wi
    ord.1
    wps
    wch
    df-or
    sylib
end
