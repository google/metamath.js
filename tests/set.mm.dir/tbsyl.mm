include "wi.mm"
include "tb-ax1.mm"
include "ax-mp.mm"

theorem tbsyl
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume tbsyl.1: |- ( ph -> ps )
  assume tbsyl.2: |- ( ps -> ch )


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
    tbsyl.2
    wph
    wps
    wi
    @0
    @1
    wi
    tbsyl.1
    wph
    wps
    wch
    tb-ax1
    ax-mp
    ax-mp
end
