include "wb.mm"
include "wa.mm"
include "bothfbothsame.mm"
include "bothtbothsame.mm"
include "pm3.2i.mm"

theorem mdandyv10
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let vk: setvar k
  let vx: setvar x
  assume mdandyv10.1: |- ( ph <-> F. )
  assume mdandyv10.2: |- ( ps <-> T. )
  assume mdandyv10.3: |- ( ch <-> F. )
  assume mdandyv10.4: |- ( th <-> T. )
  assume mdandyv10.5: |- ( ta <-> F. )
  assume mdandyv10.6: |- ( et <-> T. )


  assert |- ( ( ( ( ch <-> ph ) /\ ( th <-> ps ) ) /\ ( ta <-> ph ) ) /\ ( et <-> ps ) )

  proof
    wch
    wph
    wb
    #
    wth
    wps
    wb
    #
    wa
    #
    wta
    wph
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
    wph
    mdandyv10.3
    mdandyv10.1
    bothfbothsame
    wth
    wps
    mdandyv10.4
    mdandyv10.2
    bothtbothsame
    pm3.2i
    wta
    wph
    mdandyv10.5
    mdandyv10.1
    bothfbothsame
    pm3.2i
    wet
    wps
    mdandyv10.6
    mdandyv10.2
    bothtbothsame
    pm3.2i
end
