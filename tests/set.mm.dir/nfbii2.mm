include "wb.mm"
include "wal.mm"
include "nfa1.mm"
include "sp.mm"
include "nfbidf.mm"

theorem nfbii2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( A. x ( ph <-> ps ) -> ( F/ x ph <-> F/ x ps ) )

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
    nfbidf
end
