include "cmv.mm"
include "co.mm"
include "cno.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "c0v.mm"
include "hvsubcli.mm"
include "norm-i-i.mm"
include "hvsubeq0i.mm"
include "bitri.mm"

theorem normsub0i
  let cA: class A
  let cB: class B
  assume normsub0.1: |- A e. ~H
  assume normsub0.2: |- B e. ~H


  assert |- ( ( normh ` ( A -h B ) ) = 0 <-> A = B )

  proof
    cA
    cB
    cmv
    co
    #
    cno
    cfv
    cc0
    wceq
    @0
    c0v
    wceq
    cA
    cB
    wceq
    @0
    cA
    cB
    normsub0.1
    normsub0.2
    hvsubcli
    norm-i-i
    cA
    cB
    normsub0.1
    normsub0.2
    hvsubeq0i
    bitri
end
