include "copab.mm"
include "c0.mm"
include "wceq.mm"
include "wn.mm"
include "wal.mm"
include "wne.mm"
include "wex.mm"
include "opabn0.mm"
include "df-ne.mm"
include "2exnaln.mm"
include "3bitr3i.mm"
include "con4bii.mm"

theorem opab0
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( { <. x , y >. | ph } = (/) <-> A. x A. y -. ph )

  proof
    wph
    vx
    vy
    copab
    #
    c0
    wceq
    #
    wph
    wn
    vy
    wal
    vx
    wal
    #
    @0
    c0
    wne
    wph
    vy
    wex
    vx
    wex
    @1
    wn
    @2
    wn
    wph
    vx
    vy
    opabn0
    @0
    c0
    df-ne
    wph
    vx
    vy
    2exnaln
    3bitr3i
    con4bii
end
