include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wel.mm"
include "nfnae.mm"
include "bj-nfeel2.mm"
include "elequ2.mm"
include "bj-dvelimdv1.mm"

theorem bj-axc14nf
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t


  assert |- ( -. A. z z = x -> ( -. A. z z = y -> F/ z x e. y ) )

  proof
    vz
    vx
    weq
    vz
    wal
    wn
    vx
    vy
    wel
    vx
    vt
    wel
    vz
    vy
    vt
    vz
    vx
    vz
    nfnae
    vz
    vx
    vt
    bj-nfeel2
    vt
    vy
    vx
    elequ2
    bj-dvelimdv1
end
