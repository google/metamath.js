include "wb.mm"
include "wal.mm"
include "nfa1.mm"
include "sp.mm"
include "eubid.mm"

theorem eubi
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( A. x ( ph <-> ps ) -> ( E! x ph <-> E! x ps ) )

  proof
    wph
    wps
    wb
    #
    vx
    wal
    wph
    wps
    vx
    @0
    vx
    nfa1
    @0
    vx
    sp
    eubid
end
