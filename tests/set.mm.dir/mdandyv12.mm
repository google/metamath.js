include "wb.mm"
include "wa.mm"
include "bothfbothsame.mm"
include "pm3.2i.mm"
include "bothtbothsame.mm"

theorem mdandyv12
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let vk: setvar k
  let vx: setvar x
  assume mdandyv12.1: |- ( ph <-> F. )
  assume mdandyv12.2: |- ( ps <-> T. )
  assume mdandyv12.3: |- ( ch <-> F. )
  assume mdandyv12.4: |- ( th <-> F. )
  assume mdandyv12.5: |- ( ta <-> T. )
  assume mdandyv12.6: |- ( et <-> T. )


  assert |- ( ( ( ( ch <-> ph ) /\ ( th <-> ph ) ) /\ ( ta <-> ps ) ) /\ ( et <-> ps ) )

  proof
    wch
    wph
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
    wph
    mdandyv12.3
    mdandyv12.1
    bothfbothsame
    wth
    wph
    mdandyv12.4
    mdandyv12.1
    bothfbothsame
    pm3.2i
    wta
    wps
    mdandyv12.5
    mdandyv12.2
    bothtbothsame
    pm3.2i
    wet
    wps
    mdandyv12.6
    mdandyv12.2
    bothtbothsame
    pm3.2i
end
