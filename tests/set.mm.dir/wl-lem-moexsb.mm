include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "wsb.mm"
include "nfa1.mm"
include "nfs1v.mm"
include "sp.mm"
include "ax12v2.mm"
include "syli.mm"
include "sb2.mm"
include "syl6.mm"
include "exlimd.mm"
include "spsbe.mm"
include "impbid1.mm"

theorem wl-lem-moexsb
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z

  disjoint x z
  assert |- ( A. x ( ph -> x = z ) -> ( E. x ph <-> [ z / x ] ph ) )

  proof
    wph
    vx
    vz
    weq
    #
    wi
    #
    vx
    wal
    #
    wph
    vx
    wex
    wph
    vx
    vz
    wsb
    #
    @2
    wph
    @3
    vx
    @1
    vx
    nfa1
    wph
    vx
    vz
    nfs1v
    @2
    wph
    @0
    wph
    wi
    vx
    wal
    #
    @3
    wph
    @2
    @0
    @4
    @1
    vx
    sp
    wph
    vx
    vz
    ax12v2
    syli
    wph
    vx
    vz
    sb2
    syl6
    exlimd
    wph
    vx
    vz
    spsbe
    impbid1
end
