include "cun.mm"
include "cort.mm"
include "cfv.mm"
include "chj.mm"
include "co.mm"
include "chil.mm"
include "wss.mm"
include "shssii.mm"
include "unssi.mm"
include "ococss.mm"
include "ax-mp.mm"
include "csh.mm"
include "wcel.mm"
include "wceq.mm"
include "shjval.mm"
include "mp2an.mm"
include "sseqtr4i.mm"

theorem shunssji
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


  assert |- ( A u. B ) C_ ( A vH B )

  proof
    cA
    cB
    cun
    #
    @0
    cort
    cfv
    cort
    cfv
    #
    cA
    cB
    chj
    co
    #
    @0
    chil
    wss
    @0
    @1
    wss
    cA
    cB
    chil
    cA
    shincl.1
    shssii
    cB
    shincl.2
    shssii
    unssi
    @0
    ococss
    ax-mp
    cA
    csh
    wcel
    cB
    csh
    wcel
    @2
    @1
    wceq
    shincl.1
    shincl.2
    cA
    cB
    shjval
    mp2an
    sseqtr4i
end
