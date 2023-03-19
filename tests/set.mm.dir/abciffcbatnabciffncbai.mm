include "wa.mm"
include "wn.mm"
include "wb.mm"
include "notbi.mm"
include "biimpi.mm"
include "ax-mp.mm"

theorem abciffcbatnabciffncbai
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vk: setvar k
  let vx: setvar x
  assume abciffcbatnabciffncbai.1: |- ( ( ( ph /\ ps ) /\ ch ) <-> ( ( ch /\ ps ) /\ ph ) )


  assert |- ( -. ( ( ph /\ ps ) /\ ch ) -> -. ( ( ch /\ ps ) /\ ph ) )

  proof
    wph
    wps
    wa
    wch
    wa
    #
    wn
    #
    wch
    wps
    wa
    wph
    wa
    #
    wn
    #
    @0
    @2
    wb
    #
    @1
    @3
    wb
    #
    abciffcbatnabciffncbai.1
    @4
    @5
    @0
    @2
    notbi
    biimpi
    ax-mp
    biimpi
end
