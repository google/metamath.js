include "wi.mm"
include "w3a.mm"
include "w3o.mm"
include "3pm3.2i.mm"
include "3jao.mm"
include "ax-mp.mm"

theorem 3jaoi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume 3jaoi.1: |- ( ph -> ps )
  assume 3jaoi.2: |- ( ch -> ps )
  assume 3jaoi.3: |- ( th -> ps )


  assert |- ( ( ph \/ ch \/ th ) -> ps )

  proof
    wph
    wps
    wi
    #
    wch
    wps
    wi
    #
    wth
    wps
    wi
    #
    w3a
    wph
    wch
    wth
    w3o
    wps
    wi
    @0
    @1
    @2
    3jaoi.1
    3jaoi.2
    3jaoi.3
    3pm3.2i
    wph
    wps
    wch
    wth
    3jao
    ax-mp
end
