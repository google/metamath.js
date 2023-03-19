include "chil.mm"
include "wss.mm"
include "cspn.mm"
include "cfv.mm"
include "cort.mm"
include "ocss.mm"
include "syl.mm"
include "ococss.mm"
include "spanss.mm"
include "syl2anc.mm"
include "csh.mm"
include "wcel.mm"
include "wceq.mm"
include "ocsh.mm"
include "spanid.mm"
include "3syl.mm"
include "sseqtrd.mm"

theorem spanssoc
  let cA: class A
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( A C_ ~H -> ( span ` A ) C_ ( _|_ ` ( _|_ ` A ) ) )

  proof
    cA
    chil
    wss
    #
    cA
    cspn
    cfv
    #
    cA
    cort
    cfv
    #
    cort
    cfv
    #
    cspn
    cfv
    #
    @3
    @0
    @3
    chil
    wss
    #
    cA
    @3
    wss
    @1
    @4
    wss
    @0
    @2
    chil
    wss
    #
    @5
    cA
    ocss
    #
    @2
    ocss
    syl
    cA
    ococss
    cA
    @3
    spanss
    syl2anc
    @0
    @6
    @3
    csh
    wcel
    @4
    @3
    wceq
    @7
    @2
    ocsh
    @3
    spanid
    3syl
    sseqtrd
end
