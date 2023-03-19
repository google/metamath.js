include "chil.mm"
include "cpw.mm"
include "wss.mm"
include "wa.mm"
include "cuni.mm"
include "cort.mm"
include "cfv.mm"
include "chsup.mm"
include "uniss.mm"
include "wi.mm"
include "sspwuni.mm"
include "occon2.mm"
include "syl2anb.mm"
include "syl5.mm"
include "wceq.mm"
include "hsupval.mm"
include "adantr.mm"
include "adantl.mm"
include "sseq12d.mm"
include "sylibrd.mm"

theorem hsupss
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cD: class D


  assert |- ( ( A C_ ~P ~H /\ B C_ ~P ~H ) -> ( A C_ B -> ( \/H ` A ) C_ ( \/H ` B ) ) )

  proof
    cA
    chil
    cpw
    #
    wss
    #
    cB
    @0
    wss
    #
    wa
    #
    cA
    cB
    wss
    #
    cA
    cuni
    #
    cort
    cfv
    cort
    cfv
    #
    cB
    cuni
    #
    cort
    cfv
    cort
    cfv
    #
    wss
    #
    cA
    chsup
    cfv
    #
    cB
    chsup
    cfv
    #
    wss
    @4
    @5
    @7
    wss
    #
    @3
    @9
    cA
    cB
    uniss
    @1
    @5
    chil
    wss
    @7
    chil
    wss
    @12
    @9
    wi
    @2
    cA
    chil
    sspwuni
    cB
    chil
    sspwuni
    @5
    @7
    occon2
    syl2anb
    syl5
    @3
    @10
    @6
    @11
    @8
    @1
    @10
    @6
    wceq
    @2
    cA
    hsupval
    adantr
    @2
    @11
    @8
    wceq
    @1
    cB
    hsupval
    adantl
    sseq12d
    sylibrd
end
