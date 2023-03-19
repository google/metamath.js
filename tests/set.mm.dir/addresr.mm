include "cnr.mm"
include "wcel.mm"
include "wa.mm"
include "c0r.mm"
include "cop.mm"
include "caddc.mm"
include "co.mm"
include "cplr.mm"
include "wceq.mm"
include "0r.mm"
include "addcnsr.mm"
include "an4s.mm"
include "mpanr12.mm"
include "0idsr.mm"
include "ax-mp.mm"
include "opeq2i.mm"
include "syl6eq.mm"

theorem addresr
  let cA: class A
  let cB: class B


  assert |- ( ( A e. R. /\ B e. R. ) -> ( <. A , 0R >. + <. B , 0R >. ) = <. ( A +R B ) , 0R >. )

  proof
    cA
    cnr
    wcel
    #
    cB
    cnr
    wcel
    #
    wa
    #
    cA
    c0r
    cop
    cB
    c0r
    cop
    caddc
    co
    #
    cA
    cB
    cplr
    co
    #
    c0r
    c0r
    cplr
    co
    #
    cop
    #
    @4
    c0r
    cop
    @2
    c0r
    cnr
    wcel
    #
    @7
    @3
    @6
    wceq
    #
    0r
    0r
    @0
    @7
    @1
    @7
    @8
    cA
    c0r
    cB
    c0r
    addcnsr
    an4s
    mpanr12
    @5
    c0r
    @4
    @7
    @5
    c0r
    wceq
    0r
    c0r
    0idsr
    ax-mp
    opeq2i
    syl6eq
end
