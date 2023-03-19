include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wnfc.mm"
include "wi.mm"
include "wtru.mm"
include "nftru.mm"
include "a1i.mm"
include "wceq.mm"
include "dvelimdc.mm"
include "trud.mm"

theorem dvelimc
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  assume dvelimc.1: |- F/_ x A
  assume dvelimc.2: |- F/_ z B
  assume dvelimc.3: |- ( z = y -> A = B )


  assert |- ( -. A. x x = y -> F/_ x B )

  proof
    vx
    vy
    weq
    vx
    wal
    wn
    vx
    cB
    wnfc
    wi
    wtru
    vx
    vy
    vz
    cA
    cB
    vx
    nftru
    vz
    nftru
    vx
    cA
    wnfc
    wtru
    dvelimc.1
    a1i
    vz
    cB
    wnfc
    wtru
    dvelimc.2
    a1i
    vz
    vy
    weq
    cA
    cB
    wceq
    wi
    wtru
    dvelimc.3
    a1i
    dvelimdc
    trud
end
