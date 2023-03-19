include "csh.mm"
include "wcel.mm"
include "cph.mm"
include "co.mm"
include "wceq.mm"
include "shscom.mm"
include "mp2an.mm"

theorem shscomi
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


  assert |- ( A +H B ) = ( B +H A )

  proof
    cA
    csh
    wcel
    cB
    csh
    wcel
    cA
    cB
    cph
    co
    cB
    cA
    cph
    co
    wceq
    shincl.1
    shincl.2
    cA
    cB
    shscom
    mp2an
end
