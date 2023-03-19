include "wal.mm"
include "wn.mm"
include "wex.mm"
include "alex.mm"
include "19.8a.mm"
include "con1i.mm"
include "sylbi.mm"

theorem sp
  param wph: wff ph
  param vx: setvar x


  assert |- ( A. x ph -> ph )

  proof
    wph
    vx
    wal
    wph
    wn
    #
    vx
    wex
    #
    wn
    wph
    wph
    vx
    alex
    wph
    @1
    @0
    vx
    19.8a
    con1i
    sylbi
end
