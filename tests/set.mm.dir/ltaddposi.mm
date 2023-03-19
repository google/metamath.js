include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "caddc.mm"
include "co.mm"
include "wb.mm"
include "ltaddpos.mm"
include "mp2an.mm"

theorem ltaddposi
  let cA: class A
  let cB: class B
  assume lt2.1: |- A e. RR
  assume lt2.2: |- B e. RR


  assert |- ( 0 < A <-> B < ( B + A ) )

  proof
    cA
    cr
    wcel
    cB
    cr
    wcel
    cc0
    cA
    clt
    wbr
    cB
    cB
    cA
    caddc
    co
    clt
    wbr
    wb
    lt2.1
    lt2.2
    cA
    cB
    ltaddpos
    mp2an
end
