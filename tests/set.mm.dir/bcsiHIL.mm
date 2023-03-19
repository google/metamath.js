include "csp.mm"
include "cva.mm"
include "csm.mm"
include "cop.mm"
include "cno.mm"
include "chil.mm"
include "df-hba.mm"
include "eqid.mm"
include "hhnm.mm"
include "hhip.mm"
include "hhph.mm"
include "siii.mm"

theorem bcsiHIL
  let cA: class A
  let cB: class B
  assume bcs.1: |- A e. ~H
  assume bcs.2: |- B e. ~H


  assert |- ( abs ` ( A .ih B ) ) <_ ( ( normh ` A ) x. ( normh ` B ) )

  proof
    cA
    cB
    csp
    cva
    csm
    cop
    cno
    cop
    #
    cno
    chil
    df-hba
    @0
    @0
    eqid
    #
    hhnm
    @0
    @1
    hhip
    @0
    @1
    hhph
    bcs.1
    bcs.2
    siii
end
