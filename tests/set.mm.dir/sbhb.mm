include "wal.mm"
include "wi.mm"
include "wsb.mm"
include "nfv.mm"
include "sb8.mm"
include "imbi2i.mm"
include "19.21v.mm"
include "bitr4i.mm"

theorem sbhb
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y

  disjoint ph y
  assert |- ( ( ph -> A. x ph ) <-> A. y ( ph -> [ y / x ] ph ) )

  proof
    wph
    wph
    vx
    wal
    #
    wi
    wph
    wph
    vx
    vy
    wsb
    #
    vy
    wal
    #
    wi
    wph
    @1
    wi
    vy
    wal
    @0
    @2
    wph
    wph
    vx
    vy
    wph
    vy
    nfv
    sb8
    imbi2i
    wph
    @1
    vy
    19.21v
    bitr4i
end
