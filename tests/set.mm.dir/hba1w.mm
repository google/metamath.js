include "wal.mm"
include "wn.mm"
include "wb.mm"
include "weq.mm"
include "cbvalvw.mm"
include "notbii.mm"
include "a1i.mm"
include "spw.mm"
include "con2i.mm"
include "hbn1w.mm"
include "con1i.mm"
include "alimi.mm"
include "3syl.mm"

theorem hba1w
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume hbn1w.1: |- ( x = y -> ( ph <-> ps ) )

  disjoint ph y
  disjoint ps x
  disjoint x y
  assert |- ( A. x ph -> A. x A. x ph )

  proof
    wph
    vx
    wal
    #
    @0
    wn
    #
    vx
    wal
    #
    wn
    #
    @3
    vx
    wal
    @0
    vx
    wal
    @2
    @0
    @1
    wps
    vy
    wal
    #
    wn
    #
    vx
    vy
    @1
    @5
    wb
    vx
    vy
    weq
    @0
    @4
    wph
    wps
    vx
    vy
    hbn1w.1
    cbvalvw
    notbii
    a1i
    #
    spw
    con2i
    @1
    @5
    vx
    vy
    @6
    hbn1w
    @3
    @0
    vx
    @0
    @2
    wph
    wps
    vx
    vy
    hbn1w.1
    hbn1w
    con1i
    alimi
    3syl
end
