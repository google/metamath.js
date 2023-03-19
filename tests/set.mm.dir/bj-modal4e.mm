include "wex.mm"
include "wn.mm"
include "wal.mm"
include "hba1.mm"
include "alnex.mm"
include "2exnaln.mm"
include "con2bii.mm"
include "3imtr3i.mm"
include "con4i.mm"

theorem bj-modal4e
  let wph: wff ph
  let vx: setvar x


  assert |- ( E. x E. x ph -> E. x ph )

  proof
    wph
    vx
    wex
    #
    @0
    vx
    wex
    #
    wph
    wn
    #
    vx
    wal
    #
    @3
    vx
    wal
    #
    @0
    wn
    @1
    wn
    @2
    vx
    hba1
    wph
    vx
    alnex
    @1
    @4
    wph
    vx
    vx
    2exnaln
    con2bii
    3imtr3i
    con4i
end
