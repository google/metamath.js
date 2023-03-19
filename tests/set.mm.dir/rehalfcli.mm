include "cr.mm"
include "wcel.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "rehalfcl.mm"
include "ax-mp.mm"

theorem rehalfcli
  let cA: class A
  assume rehalfcli.1: |- A e. RR


  assert |- ( A / 2 ) e. RR

  proof
    cA
    cr
    wcel
    cA
    c2
    cdiv
    co
    cr
    wcel
    rehalfcli.1
    cA
    rehalfcl
    ax-mp
end
