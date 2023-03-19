include "ccnv.mm"
include "cuni.mm"
include "crn.mm"
include "cdm.mm"
include "cun.mm"
include "wrel.mm"
include "wceq.mm"
include "relcnv.mm"
include "relfld.mm"
include "ax-mp.mm"
include "equncomi.mm"
include "dfdm4.mm"
include "df-rn.mm"
include "uneq12i.mm"
include "eqtr4i.mm"

theorem unidmrn
  let cA: class A


  assert |- U. U. `' A = ( dom A u. ran A )

  proof
    cA
    ccnv
    #
    cuni
    cuni
    #
    @0
    crn
    #
    @0
    cdm
    #
    cun
    cA
    cdm
    #
    cA
    crn
    #
    cun
    @1
    @3
    @2
    @0
    wrel
    @1
    @3
    @2
    cun
    wceq
    cA
    relcnv
    @0
    relfld
    ax-mp
    equncomi
    @4
    @2
    @5
    @3
    cA
    dfdm4
    cA
    df-rn
    uneq12i
    eqtr4i
end
