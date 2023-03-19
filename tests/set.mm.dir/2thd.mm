include "wb.mm"
include "pm5.1im.mm"
include "sylc.mm"

theorem 2thd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume 2thd.1: |- ( ph -> ps )
  assume 2thd.2: |- ( ph -> ch )


  assert |- ( ph -> ( ps <-> ch ) )

  proof
    wph
    wps
    wch
    wps
    wch
    wb
    2thd.1
    2thd.2
    wps
    wch
    pm5.1im
    sylc
end
