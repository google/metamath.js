include "wex.mm"
include "wn.mm"
include "wal.mm"
include "df-ex.mm"
include "weq.mm"
include "wa.mm"
include "nfnd.mm"
include "nfald2.mm"
include "nfxfrd.mm"

theorem nfexd2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume nfald2.1: |- F/ y ph
  assume nfald2.2: |- ( ( ph /\ -. A. x x = y ) -> F/ x ps )


  assert |- ( ph -> F/ x E. y ps )

  proof
    wps
    vy
    wex
    wps
    wn
    #
    vy
    wal
    #
    wn
    wph
    vx
    wps
    vy
    df-ex
    wph
    @1
    vx
    wph
    @0
    vx
    vy
    nfald2.1
    wph
    vx
    vy
    weq
    vx
    wal
    wn
    wa
    wps
    vx
    nfald2.2
    nfnd
    nfald2
    nfnd
    nfxfrd
end
