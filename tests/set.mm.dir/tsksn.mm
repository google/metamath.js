include "ctsk.mm"
include "wcel.mm"
include "cpw.mm"
include "csn.mm"
include "tskpw.mm"
include "wss.mm"
include "snsspw.mm"
include "tskss.mm"
include "mp3an3.mm"
include "syldan.mm"

theorem tsksn
  let cA: class A
  let cT: class T


  assert |- ( ( T e. Tarski /\ A e. T ) -> { A } e. T )

  proof
    cT
    ctsk
    wcel
    #
    cA
    cT
    wcel
    cA
    cpw
    #
    cT
    wcel
    #
    cA
    csn
    #
    cT
    wcel
    #
    cA
    cT
    tskpw
    @0
    @2
    @3
    @1
    wss
    @4
    cA
    snsspw
    @1
    @3
    cT
    tskss
    mp3an3
    syldan
end
