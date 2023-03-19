include "wsb.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "sbf.mm"
include "biidd.mm"
include "equsal.mm"
include "bitr4i.mm"

theorem sb6x
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assume sb6x.1: |- F/ x ph


  assert |- ( [ y / x ] ph <-> A. x ( x = y -> ph ) )

  proof
    wph
    vx
    vy
    wsb
    wph
    vx
    vy
    weq
    #
    wph
    wi
    vx
    wal
    wph
    vx
    vy
    sb6x.1
    sbf
    wph
    wph
    vx
    vy
    sb6x.1
    @0
    wph
    biidd
    equsal
    bitr4i
end
