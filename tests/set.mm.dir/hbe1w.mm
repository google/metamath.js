include "wex.mm"
include "wn.mm"
include "wal.mm"
include "df-ex.mm"
include "weq.mm"
include "notbid.mm"
include "hbn1w.mm"
include "hbxfrbi.mm"

theorem hbe1w
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume hbn1w.1: |- ( x = y -> ( ph <-> ps ) )

  disjoint ph y
  disjoint ps x
  disjoint x y
  assert |- ( E. x ph -> A. x E. x ph )

  proof
    wph
    vx
    wex
    wph
    wn
    #
    vx
    wal
    wn
    vx
    wph
    vx
    df-ex
    @0
    wps
    wn
    vx
    vy
    vx
    vy
    weq
    wph
    wps
    hbn1w.1
    notbid
    hbn1w
    hbxfrbi
end
