include "wss.mm"
include "cort.mm"
include "cfv.mm"
include "cin.mm"
include "chj.mm"
include "co.mm"
include "c0h.mm"
include "wceq.mm"
include "inss2.mm"
include "choccli.mm"
include "chincli.mm"
include "chlubii.mm"
include "mpan2.mm"
include "chdmj1i.mm"
include "ineq2i.mm"
include "incom.mm"
include "ineq1i.mm"
include "inass.mm"
include "chocini.mm"
include "3eqtr3i.mm"
include "eqtri.mm"
include "chjcli.mm"
include "chshii.mm"
include "pjomli.mm"
include "sylancl.mm"

theorem pjoml2i
  let cA: class A
  let cB: class B
  let vx: setvar x
  assume pjoml2.1: |- A e. CH
  assume pjoml2.2: |- B e. CH


  assert |- ( A C_ B -> ( A vH ( ( _|_ ` A ) i^i B ) ) = B )

  proof
    cA
    cB
    wss
    #
    cA
    cA
    cort
    cfv
    #
    cB
    cin
    #
    chj
    co
    #
    cB
    wss
    #
    cB
    @3
    cort
    cfv
    #
    cin
    #
    c0h
    wceq
    @3
    cB
    wceq
    @0
    @2
    cB
    wss
    @4
    @1
    cB
    inss2
    cA
    @2
    cB
    pjoml2.1
    @1
    cB
    cA
    pjoml2.1
    choccli
    pjoml2.2
    chincli
    #
    pjoml2.2
    chlubii
    mpan2
    @6
    cB
    @1
    @2
    cort
    cfv
    #
    cin
    #
    cin
    #
    c0h
    @5
    @9
    cB
    cA
    @2
    pjoml2.1
    @7
    chdmj1i
    ineq2i
    cB
    @1
    cin
    #
    @8
    cin
    @2
    @8
    cin
    @10
    c0h
    @11
    @2
    @8
    cB
    @1
    incom
    ineq1i
    cB
    @1
    @8
    inass
    @2
    @7
    chocini
    3eqtr3i
    eqtri
    @3
    cB
    cA
    @2
    pjoml2.1
    @7
    chjcli
    cB
    pjoml2.2
    chshii
    pjomli
    sylancl
end
