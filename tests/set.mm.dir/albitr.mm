include "wb.mm"
include "bitr.mm"
include "alanimi.mm"

theorem albitr
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x


  assert |- ( ( A. x ( ph <-> ps ) /\ A. x ( ps <-> ch ) ) -> A. x ( ph <-> ch ) )

  proof
    wph
    wps
    wb
    wps
    wch
    wb
    wph
    wch
    wb
    vx
    wph
    wps
    wch
    bitr
    alanimi
end
