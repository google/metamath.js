include "wnf.mm"
include "wssb.mm"
include "wex.mm"
include "wal.mm"
include "bj-sbex.mm"
include "wi.mm"
include "df-nf.mm"
include "biimpi.mm"
include "sp.mm"
include "syl56.mm"
include "19.8a.mm"
include "bj-alsb.mm"
include "impbid.mm"

theorem bj-ssbft
  let wph: wff ph
  let vx: setvar x
  let vt: setvar t


  assert |- ( F/ x ph -> ( [b t /b x ]b ph <-> ph ) )

  proof
    wph
    vx
    wnf
    #
    wph
    vx
    vt
    wssb
    #
    wph
    @1
    wph
    vx
    wex
    #
    @0
    wph
    vx
    wal
    #
    wph
    wph
    vx
    vt
    bj-sbex
    @0
    @2
    @3
    wi
    wph
    vx
    df-nf
    biimpi
    #
    wph
    vx
    sp
    syl56
    wph
    @2
    @0
    @3
    @1
    wph
    vx
    19.8a
    @4
    wph
    vx
    vt
    bj-alsb
    syl56
    impbid
end
