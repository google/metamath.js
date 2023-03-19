include "csh.mm"
include "wcel.mm"
include "cph.mm"
include "co.mm"
include "wi.mm"
include "shsel1.mm"
include "mp2an.mm"

theorem shsel1i
  let cA: class A
  let cB: class B
  let cC: class C
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cD: class D
  assume shincl.1: |- A e. SH
  assume shincl.2: |- B e. SH


  assert |- ( C e. A -> C e. ( A +H B ) )

  proof
    cA
    csh
    wcel
    cB
    csh
    wcel
    cC
    cA
    wcel
    cC
    cA
    cB
    cph
    co
    wcel
    wi
    shincl.1
    shincl.2
    cA
    cB
    cC
    shsel1
    mp2an
end
