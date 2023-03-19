include "wb.mm"
include "wa.mm"
include "bothtbothsame.mm"
include "pm3.2i.mm"

theorem mdandyv15
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let vk: setvar k
  let vx: setvar x
  assume mdandyv15.1: |- ( ph <-> F. )
  assume mdandyv15.2: |- ( ps <-> T. )
  assume mdandyv15.3: |- ( ch <-> T. )
  assume mdandyv15.4: |- ( th <-> T. )
  assume mdandyv15.5: |- ( ta <-> T. )
  assume mdandyv15.6: |- ( et <-> T. )


  assert |- ( ( ( ( ch <-> ps ) /\ ( th <-> ps ) ) /\ ( ta <-> ps ) ) /\ ( et <-> ps ) )

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
    mdandyv15.3
    mdandyv15.2
    bothtbothsame
    wth
    wps
    mdandyv15.4
    mdandyv15.2
    bothtbothsame
    pm3.2i
    wta
    wps
    mdandyv15.5
    mdandyv15.2
    bothtbothsame
    pm3.2i
    wet
    wps
    mdandyv15.6
    mdandyv15.2
    bothtbothsame
    pm3.2i
end
