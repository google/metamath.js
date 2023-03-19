include "wb.mm"
include "wa.mm"
include "bothtbothsame.mm"
include "bothfbothsame.mm"
include "pm3.2i.mm"

theorem mdandyv13
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let vk: setvar k
  let vx: setvar x
  assume mdandyv13.1: |- ( ph <-> F. )
  assume mdandyv13.2: |- ( ps <-> T. )
  assume mdandyv13.3: |- ( ch <-> T. )
  assume mdandyv13.4: |- ( th <-> F. )
  assume mdandyv13.5: |- ( ta <-> T. )
  assume mdandyv13.6: |- ( et <-> T. )


  assert |- ( ( ( ( ch <-> ps ) /\ ( th <-> ph ) ) /\ ( ta <-> ps ) ) /\ ( et <-> ps ) )

  proof
    wch
    wps
    wb
    #
    wth
    wph
    wb
    #
    wa
    #
    wta
    wps
    wb
    #
    wa
    wet
    wps
    wb
    @2
    @3
    @0
    @1
    wch
    wps
    mdandyv13.3
    mdandyv13.2
    bothtbothsame
    wth
    wph
    mdandyv13.4
    mdandyv13.1
    bothfbothsame
    pm3.2i
    wta
    wps
    mdandyv13.5
    mdandyv13.2
    bothtbothsame
    pm3.2i
    wet
    wps
    mdandyv13.6
    mdandyv13.2
    bothtbothsame
    pm3.2i
end
