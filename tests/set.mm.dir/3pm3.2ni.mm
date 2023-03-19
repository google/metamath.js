include "w3o.mm"
include "wo.mm"
include "pm3.2ni.mm"
include "df-3or.mm"
include "mtbir.mm"

theorem 3pm3.2ni
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume 3pm3.2ni.1: |- -. ph
  assume 3pm3.2ni.2: |- -. ps
  assume 3pm3.2ni.3: |- -. ch


  assert |- -. ( ph \/ ps \/ ch )

  proof
    wph
    wps
    wch
    w3o
    wph
    wps
    wo
    #
    wch
    wo
    @0
    wch
    wph
    wps
    3pm3.2ni.1
    3pm3.2ni.2
    pm3.2ni
    3pm3.2ni.3
    pm3.2ni
    wph
    wps
    wch
    df-3or
    mtbir
end
