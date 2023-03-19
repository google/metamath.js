include "wcel.mm"
include "cen.mm"
include "wbr.mm"
include "cid.mm"
include "cres.mm"
include "wf1o.mm"
include "f1oi.mm"
include "f1oen2g.mm"
include "mp3an3.mm"
include "anidms.mm"

theorem enrefg
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> A ~~ A )

  proof
    cA
    cV
    wcel
    #
    cA
    cA
    cen
    wbr
    #
    @0
    @0
    cA
    cA
    cid
    cA
    cres
    #
    wf1o
    @1
    cA
    f1oi
    cA
    cA
    @2
    cV
    cV
    f1oen2g
    mp3an3
    anidms
end
