include "wo.mm"
include "w3o.mm"
include "df-3or.mm"
include "sylbir.mm"
include "orcs.mm"

theorem 3o1cs
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume 3o1cs.1: |- ( ( ph \/ ps \/ ch ) -> th )


  assert |- ( ph -> th )

  proof
    wph
    wps
    wth
    wph
    wps
    wo
    #
    wch
    wth
    @0
    wch
    wo
    wph
    wps
    wch
    w3o
    wth
    wph
    wps
    wch
    df-3or
    3o1cs.1
    sylbir
    orcs
    orcs
end
