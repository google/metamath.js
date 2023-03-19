include "cioo.mm"
include "co.mm"
include "cr.mm"
include "cc.mm"
include "ioossre.mm"
include "ax-resscn.mm"
include "sstri.mm"

theorem ioosscn
  let cA: class A
  let cB: class B


  assert |- ( A (,) B ) C_ CC

  proof
    cA
    cB
    cioo
    co
    cr
    cc
    cA
    cB
    ioossre
    ax-resscn
    sstri
end
