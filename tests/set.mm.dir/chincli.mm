include "cpr.mm"
include "cint.mm"
include "cin.mm"
include "cch.mm"
include "elexi.mm"
include "intpr.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wcel.mm"
include "wa.mm"
include "pm3.2i.mm"
include "prss.mm"
include "mpbi.mm"
include "prnz.mm"
include "chintcli.mm"
include "eqeltrri.mm"

theorem chincli
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  assume ch0le.1: |- A e. CH
  assume chjcl.2: |- B e. CH


  assert |- ( A i^i B ) e. CH

  proof
    cA
    cB
    cpr
    #
    cint
    cA
    cB
    cin
    cch
    cA
    cB
    cA
    cch
    ch0le.1
    elexi
    #
    cB
    cch
    chjcl.2
    elexi
    #
    intpr
    @0
    @0
    cch
    wss
    #
    @0
    c0
    wne
    cA
    cch
    wcel
    #
    cB
    cch
    wcel
    #
    wa
    @3
    @4
    @5
    ch0le.1
    chjcl.2
    pm3.2i
    cA
    cB
    cch
    @1
    @2
    prss
    mpbi
    cA
    cB
    @1
    prnz
    pm3.2i
    chintcli
    eqeltrri
end
