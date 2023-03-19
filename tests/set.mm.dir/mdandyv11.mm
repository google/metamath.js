include "wb.mm"
include "wa.mm"
include "bothtbothsame.mm"
include "pm3.2i.mm"
include "bothfbothsame.mm"

theorem mdandyv11
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let vk: setvar k
  let vx: setvar x
  assume mdandyv11.1: |- ( ph <-> F. )
  assume mdandyv11.2: |- ( ps <-> T. )
  assume mdandyv11.3: |- ( ch <-> T. )
  assume mdandyv11.4: |- ( th <-> T. )
  assume mdandyv11.5: |- ( ta <-> F. )
  assume mdandyv11.6: |- ( et <-> T. )


  assert |- ( ( ( ( ch <-> ps ) /\ ( th <-> ps ) ) /\ ( ta <-> ph ) ) /\ ( et <-> ps ) )

  proof
    wch
    wps
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
    wps
    mdandyv11.3
    mdandyv11.2
    bothtbothsame
    wth
    wps
    mdandyv11.4
    mdandyv11.2
    bothtbothsame
    pm3.2i
    wta
    wph
    mdandyv11.5
    mdandyv11.1
    bothfbothsame
    pm3.2i
    wet
    wps
    mdandyv11.6
    mdandyv11.2
    bothtbothsame
    pm3.2i
end
