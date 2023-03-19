include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wnf.mm"
include "wi.mm"
include "wtru.mm"
include "nfv.mm"
include "a1i.mm"
include "bj-dvelimdv1.mm"
include "trud.mm"

theorem bj-dvelimv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume bj-dvelimv.nf: |- F/ x ps
  assume bj-dvelimv.is: |- ( z = y -> ( ps <-> ph ) )

  disjoint x z
  disjoint y z
  disjoint ph z
  assert |- ( -. A. x x = y -> F/ x ph )

  proof
    vx
    vy
    weq
    vx
    wal
    wn
    wph
    vx
    wnf
    wi
    wtru
    wph
    wps
    vx
    vy
    vz
    wtru
    vx
    nfv
    wps
    vx
    wnf
    wtru
    bj-dvelimv.nf
    a1i
    bj-dvelimv.is
    bj-dvelimdv1
    trud
end
