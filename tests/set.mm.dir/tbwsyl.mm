include "wi.mm"
include "tbw-ax1.mm"
include "ax-mp.mm"

theorem tbwsyl
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume tbwsyl.1: |- ( ph -> ps )
  assume tbwsyl.2: |- ( ps -> ch )


  assert |- ( ph -> ch )

  proof
    wps
    wch
    wi
    #
    wph
    wch
    wi
    #
    tbwsyl.2
    wph
    wps
    wi
    @0
    @1
    wi
    tbwsyl.1
    wph
    wps
    wch
    tbw-ax1
    ax-mp
    ax-mp
end
