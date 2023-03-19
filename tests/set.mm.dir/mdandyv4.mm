include "wb.mm"
include "wa.mm"
include "bothfbothsame.mm"
include "pm3.2i.mm"
include "bothtbothsame.mm"

theorem mdandyv4
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let vk: setvar k
  let vx: setvar x
  assume mdandyv4.1: |- ( ph <-> F. )
  assume mdandyv4.2: |- ( ps <-> T. )
  assume mdandyv4.3: |- ( ch <-> F. )
  assume mdandyv4.4: |- ( th <-> F. )
  assume mdandyv4.5: |- ( ta <-> T. )
  assume mdandyv4.6: |- ( et <-> F. )


  assert |- ( ( ( ( ch <-> ph ) /\ ( th <-> ph ) ) /\ ( ta <-> ps ) ) /\ ( et <-> ph ) )

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
    wph
    wb
    @2
    @3
    @0
    @1
    wch
    wph
    mdandyv4.3
    mdandyv4.1
    bothfbothsame
    wth
    wph
    mdandyv4.4
    mdandyv4.1
    bothfbothsame
    pm3.2i
    wta
    wps
    mdandyv4.5
    mdandyv4.2
    bothtbothsame
    pm3.2i
    wet
    wph
    mdandyv4.6
    mdandyv4.1
    bothfbothsame
    pm3.2i
end
