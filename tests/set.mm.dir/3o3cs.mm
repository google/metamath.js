include "wo.mm"
include "w3o.mm"
include "df-3or.mm"
include "sylbir.mm"
include "olcs.mm"

theorem 3o3cs
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume 3o1cs.1: |- ( ( ph \/ ps \/ ch ) -> th )


  assert |- ( ch -> th )

  proof
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
    olcs
end
