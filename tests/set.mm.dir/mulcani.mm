include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "wb.mm"
include "pm3.2i.mm"
include "mulcan.mm"
include "mp3an.mm"

theorem mulcani
  let cA: class A
  let cB: class B
  let cC: class C
  assume mulcan.1: |- A e. CC
  assume mulcan.2: |- B e. CC
  assume mulcan.3: |- C e. CC
  assume mulcan.4: |- C =/= 0


  assert |- ( ( C x. A ) = ( C x. B ) <-> A = B )

  proof
    cA
    cc
    wcel
    cB
    cc
    wcel
    cC
    cc
    wcel
    #
    cC
    cc0
    wne
    #
    wa
    cC
    cA
    cmul
    co
    cC
    cB
    cmul
    co
    wceq
    cA
    cB
    wceq
    wb
    mulcan.1
    mulcan.2
    @0
    @1
    mulcan.3
    mulcan.4
    pm3.2i
    cA
    cB
    cC
    mulcan
    mp3an
end
