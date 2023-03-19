include "cpr.mm"
include "cint.mm"
include "cin.mm"
include "csh.mm"
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
include "shintcli.mm"
include "eqeltrri.mm"

theorem shincli
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cD: class D
  assume shincl.1: |- A e. SH
  assume shincl.2: |- B e. SH


  assert |- ( A i^i B ) e. SH

  proof
    cA
    cB
    cpr
    #
    cint
    cA
    cB
    cin
    csh
    cA
    cB
    cA
    csh
    shincl.1
    elexi
    #
    cB
    csh
    shincl.2
    elexi
    #
    intpr
    @0
    @0
    csh
    wss
    #
    @0
    c0
    wne
    cA
    csh
    wcel
    #
    cB
    csh
    wcel
    #
    wa
    @3
    @4
    @5
    shincl.1
    shincl.2
    pm3.2i
    cA
    cB
    csh
    @1
    @2
    prss
    mpbi
    cA
    cB
    @1
    prnz
    pm3.2i
    shintcli
    eqeltrri
end
