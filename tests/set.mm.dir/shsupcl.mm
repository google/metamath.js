include "chil.mm"
include "cpw.mm"
include "wss.mm"
include "cuni.mm"
include "cspn.mm"
include "cfv.mm"
include "csh.mm"
include "wcel.mm"
include "uniss.mm"
include "unipw.mm"
include "syl6sseq.mm"
include "spancl.mm"
include "syl.mm"

theorem shsupcl
  let cA: class A
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( A C_ ~P ~H -> ( span ` U. A ) e. SH )

  proof
    cA
    chil
    cpw
    #
    wss
    #
    cA
    cuni
    #
    chil
    wss
    @2
    cspn
    cfv
    csh
    wcel
    @1
    @2
    @0
    cuni
    chil
    cA
    @0
    uniss
    chil
    unipw
    syl6sseq
    @2
    spancl
    syl
end
