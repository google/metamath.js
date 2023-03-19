include "wnf.mm"
include "wex.mm"
include "wal.mm"
include "wi.mm"
include "df-nf.mm"
include "sylib.mm"

theorem nfrd
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume nfrd.1: |- ( ph -> F/ x ps )


  assert |- ( ph -> ( E. x ps -> A. x ps ) )

  proof
    wph
    wps
    vx
    wnf
    wps
    vx
    wex
    wps
    vx
    wal
    wi
    nfrd.1
    wps
    vx
    df-nf
    sylib
end
