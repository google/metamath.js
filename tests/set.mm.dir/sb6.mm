include "wsb.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "wex.mm"
include "sb1.mm"
include "sb56.mm"
include "sylib.mm"
include "sb2.mm"
include "impbii.mm"

theorem sb6
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  assert |- ( [ y / x ] ph <-> A. x ( x = y -> ph ) )

  proof
    wph
    vx
    vy
    wsb
    #
    vx
    vy
    weq
    #
    wph
    wi
    vx
    wal
    #
    @0
    @1
    wph
    wa
    vx
    wex
    @2
    wph
    vx
    vy
    sb1
    wph
    vx
    vy
    sb56
    sylib
    wph
    vx
    vy
    sb2
    impbii
end
