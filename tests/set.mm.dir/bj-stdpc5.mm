include "wnf.mm"
include "wi.mm"
include "wal.mm"
include "stdpc5t.mm"
include "ax-mp.mm"

theorem bj-stdpc5
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume bj-stdpc5.1: |- F/ x ph


  assert |- ( A. x ( ph -> ps ) -> ( ph -> A. x ps ) )

  proof
    wph
    vx
    wnf
    wph
    wps
    wi
    vx
    wal
    wph
    wps
    vx
    wal
    wi
    wi
    bj-stdpc5.1
    wph
    wps
    vx
    stdpc5t
    ax-mp
end
