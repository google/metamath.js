include "wb.mm"
include "wa.mm"
include "anbi2.mm"
include "biancomd.mm"
include "syl.mm"

theorem anbi1cd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume anbi1cd.1: |- ( ph -> ( ps <-> ch ) )


  assert |- ( ph -> ( ( th /\ ps ) <-> ( ch /\ th ) ) )

  proof
    wph
    wps
    wch
    wb
    #
    wth
    wps
    wa
    #
    wch
    wth
    wa
    wb
    anbi1cd.1
    @0
    @1
    wch
    wth
    wps
    wch
    wth
    anbi2
    biancomd
    syl
end
