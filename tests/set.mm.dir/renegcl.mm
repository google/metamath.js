include "cr.mm"
include "wcel.mm"
include "cneg.mm"
include "c1.mm"
include "cif.mm"
include "wceq.mm"
include "negeq.mm"
include "eleq1d.mm"
include "1re.mm"
include "elimel.mm"
include "renegcli.mm"
include "dedth.mm"

theorem renegcl
  let cA: class A


  assert |- ( A e. RR -> -u A e. RR )

  proof
    cA
    cr
    wcel
    #
    cA
    cneg
    #
    cr
    wcel
    @0
    cA
    c1
    cif
    #
    cneg
    #
    cr
    wcel
    cA
    c1
    cA
    @2
    wceq
    @1
    @3
    cr
    cA
    @2
    negeq
    eleq1d
    @2
    cA
    c1
    cr
    1re
    elimel
    renegcli
    dedth
end
