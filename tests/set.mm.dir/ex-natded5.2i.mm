include "wa.mm"
include "ax-mp.mm"
include "pm3.2i.mm"

theorem ex-natded5.2i
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume ex-natded5.2i.1: |- ( ( ps /\ ch ) -> th )
  assume ex-natded5.2i.2: |- ( ch -> ps )
  assume ex-natded5.2i.3: |- ch


  assert |- th

  proof
    wps
    wch
    wa
    wth
    wps
    wch
    wch
    wps
    ex-natded5.2i.3
    ex-natded5.2i.2
    ax-mp
    ex-natded5.2i.3
    pm3.2i
    ex-natded5.2i.1
    ax-mp
end
