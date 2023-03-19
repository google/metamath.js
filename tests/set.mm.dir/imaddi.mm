include "cc.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "cim.mm"
include "cfv.mm"
include "wceq.mm"
include "imadd.mm"
include "mp2an.mm"

theorem imaddi
  let cA: class A
  let cB: class B
  assume recl.1: |- A e. CC
  assume readdi.2: |- B e. CC


  assert |- ( Im ` ( A + B ) ) = ( ( Im ` A ) + ( Im ` B ) )

  proof
    cA
    cc
    wcel
    cB
    cc
    wcel
    cA
    cB
    caddc
    co
    cim
    cfv
    cA
    cim
    cfv
    cB
    cim
    cfv
    caddc
    co
    wceq
    recl.1
    readdi.2
    cA
    cB
    imadd
    mp2an
end
