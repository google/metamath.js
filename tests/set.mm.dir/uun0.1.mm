include "wtru.mm"
include "wi.mm"
include "tru.mm"
include "wa.mm"
include "pm3.2i.mm"
include "simpri.mm"
include "ex.mm"
include "ax-mp.mm"

theorem uun0.1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume uun0.1.1: |- ( T. -> ph )
  assume uun0.1.2: |- ( ps -> ch )
  assume uun0.1.3: |- ( ( T. /\ ps ) -> th )


  assert |- ( ps -> th )

  proof
    wtru
    wps
    wth
    wi
    tru
    wtru
    wps
    wth
    wtru
    wph
    wi
    #
    wps
    wch
    wi
    #
    wa
    #
    wtru
    wps
    wa
    wth
    wi
    #
    @2
    @3
    @0
    @1
    uun0.1.1
    uun0.1.2
    pm3.2i
    uun0.1.3
    pm3.2i
    simpri
    ex
    ax-mp
end
