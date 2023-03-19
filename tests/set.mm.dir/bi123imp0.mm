include "wb.mm"
include "wi.mm"
include "biimp.mm"
include "syl6.mm"
include "sylbi.mm"
include "3imp.mm"

theorem bi123imp0
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume bi23imp0.1: |- ( ph <-> ( ps <-> ( ch <-> th ) ) )


  assert |- ( ( ph /\ ps /\ ch ) -> th )

  proof
    wph
    wps
    wch
    wth
    wph
    wps
    wch
    wth
    wb
    #
    wb
    #
    wps
    wch
    wth
    wi
    #
    wi
    bi23imp0.1
    @1
    wps
    @0
    @2
    wps
    @0
    biimp
    wch
    wth
    biimp
    syl6
    sylbi
    3imp
end
