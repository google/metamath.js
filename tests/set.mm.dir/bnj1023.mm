include "wi.mm"
include "wa.mm"
include "wal.mm"
include "wex.mm"
include "a1i.mm"
include "ax-gen.mm"
include "exintr.mm"
include "mp2.mm"
include "pm3.33.mm"
include "bnj101.mm"

theorem bnj1023
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume bnj1023.1: |- E. x ( ph -> ps )
  assume bnj1023.2: |- ( ps -> ch )


  assert |- E. x ( ph -> ch )

  proof
    wph
    wps
    wi
    #
    wps
    wch
    wi
    #
    wa
    #
    wph
    wch
    wi
    vx
    @0
    @1
    wi
    #
    vx
    wal
    @0
    vx
    wex
    @2
    vx
    wex
    @3
    vx
    @1
    @0
    bnj1023.2
    a1i
    ax-gen
    bnj1023.1
    @0
    @1
    vx
    exintr
    mp2
    wph
    wps
    wch
    pm3.33
    bnj101
end
