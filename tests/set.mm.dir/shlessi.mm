include "csh.mm"
include "wcel.mm"
include "wss.mm"
include "cph.mm"
include "co.mm"
include "wi.mm"
include "w3a.mm"
include "shless.mm"
include "ex.mm"
include "mp3an.mm"

theorem shlessi
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
  assume shless.1: |- C e. SH


  assert |- ( A C_ B -> ( A +H C ) C_ ( B +H C ) )

  proof
    cA
    csh
    wcel
    #
    cB
    csh
    wcel
    #
    cC
    csh
    wcel
    #
    cA
    cB
    wss
    #
    cA
    cC
    cph
    co
    cB
    cC
    cph
    co
    wss
    #
    wi
    shincl.1
    shincl.2
    shless.1
    @0
    @1
    @2
    w3a
    @3
    @4
    cA
    cB
    cC
    shless
    ex
    mp3an
end
