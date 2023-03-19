include "wnf.mm"
include "wi.mm"
include "wal.mm"
include "stdpc5t.mm"
include "wex.mm"
include "19.9t.mm"
include "imbi1d.mm"
include "19.38.mm"
include "syl6bir.mm"
include "impbid.mm"

theorem bj-19.21t
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( F/ x ph -> ( A. x ( ph -> ps ) <-> ( ph -> A. x ps ) ) )

  proof
    wph
    vx
    wnf
    #
    wph
    wps
    wi
    vx
    wal
    #
    wph
    wps
    vx
    wal
    #
    wi
    #
    wph
    wps
    vx
    stdpc5t
    @0
    @3
    wph
    vx
    wex
    #
    @2
    wi
    @1
    @0
    @4
    wph
    @2
    wph
    vx
    19.9t
    imbi1d
    wph
    wps
    vx
    19.38
    syl6bir
    impbid
end
