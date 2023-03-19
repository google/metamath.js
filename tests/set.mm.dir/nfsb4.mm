include "wnf.mm"
include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wsb.mm"
include "wi.mm"
include "nfsb4t.mm"
include "mpg.mm"

theorem nfsb4
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume nfsb4.1: |- F/ z ph


  assert |- ( -. A. z z = y -> F/ z [ y / x ] ph )

  proof
    wph
    vz
    wnf
    vz
    vy
    weq
    vz
    wal
    wn
    wph
    vx
    vy
    wsb
    vz
    wnf
    wi
    vx
    wph
    vx
    vy
    vz
    nfsb4t
    nfsb4.1
    mpg
end
