include "cima.mm"
include "c0.mm"
include "wceq.mm"
include "cres.mm"
include "crn.mm"
include "cdm.mm"
include "cin.mm"
include "df-ima.mm"
include "eqeq1i.mm"
include "dm0rn0.mm"
include "dmres.mm"
include "incom.mm"
include "eqtri.mm"
include "3bitr2i.mm"

theorem imadisj
  let cA: class A
  let cB: class B


  assert |- ( ( A " B ) = (/) <-> ( dom A i^i B ) = (/) )

  proof
    cA
    cB
    cima
    #
    c0
    wceq
    cA
    cB
    cres
    #
    crn
    #
    c0
    wceq
    @1
    cdm
    #
    c0
    wceq
    cA
    cdm
    #
    cB
    cin
    #
    c0
    wceq
    @0
    @2
    c0
    cA
    cB
    df-ima
    eqeq1i
    @1
    dm0rn0
    @3
    @5
    c0
    @3
    cB
    @4
    cin
    @5
    cA
    cB
    dmres
    cB
    @4
    incom
    eqtri
    eqeq1i
    3bitr2i
end
