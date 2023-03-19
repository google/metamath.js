include "csh.mm"
include "wss.mm"
include "cuni.mm"
include "chil.mm"
include "cspn.mm"
include "cfv.mm"
include "cpw.mm"
include "shsspwh.mm"
include "sstr.mm"
include "mpan2.mm"
include "unissd.mm"
include "unipw.mm"
include "syl6sseq.mm"
include "spanss2.mm"
include "syl.mm"

theorem shsupunss
  let cA: class A
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( A C_ SH -> U. A C_ ( span ` U. A ) )

  proof
    cA
    csh
    wss
    #
    cA
    cuni
    #
    chil
    wss
    @1
    @1
    cspn
    cfv
    wss
    @0
    @1
    chil
    cpw
    #
    cuni
    chil
    @0
    cA
    @2
    @0
    csh
    @2
    wss
    cA
    @2
    wss
    shsspwh
    cA
    csh
    @2
    sstr
    mpan2
    unissd
    chil
    unipw
    syl6sseq
    @1
    spanss2
    syl
end
