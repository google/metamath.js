include "wal.mm"
include "wi.mm"
include "wn.mm"
include "wex.mm"
include "bj-19.9htbi.mm"
include "bicomd.mm"
include "notbid.mm"
include "alnex.mm"
include "syl6bbr.mm"

theorem bj-hbntbi
  let wph: wff ph
  let vx: setvar x


  assert |- ( A. x ( ph -> A. x ph ) -> ( -. ph <-> A. x -. ph ) )

  proof
    wph
    wph
    vx
    wal
    wi
    vx
    wal
    #
    wph
    wn
    #
    wph
    vx
    wex
    #
    wn
    @1
    vx
    wal
    @0
    wph
    @2
    @0
    @2
    wph
    wph
    vx
    bj-19.9htbi
    bicomd
    notbid
    wph
    vx
    alnex
    syl6bbr
end
