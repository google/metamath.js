include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wcel.mm"
include "cxr.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cxad.mm"
include "elxrge0.mm"
include "xaddcl.mm"
include "ad2ant2r.mm"
include "xaddge0.mm"
include "an4s.mm"
include "sylanbrc.mm"
include "syl2anb.mm"

theorem ge0xaddcl
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ( 0 [,] +oo ) /\ B e. ( 0 [,] +oo ) ) -> ( A +e B ) e. ( 0 [,] +oo ) )

  proof
    cA
    cc0
    cpnf
    cicc
    co
    #
    wcel
    cA
    cxr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    wa
    #
    cB
    cxr
    wcel
    #
    cc0
    cB
    cle
    wbr
    #
    wa
    #
    cA
    cB
    cxad
    co
    #
    @0
    wcel
    #
    cB
    @0
    wcel
    cA
    elxrge0
    cB
    elxrge0
    @3
    @6
    wa
    @7
    cxr
    wcel
    #
    cc0
    @7
    cle
    wbr
    #
    @8
    @1
    @4
    @9
    @2
    @5
    cA
    cB
    xaddcl
    ad2ant2r
    @1
    @4
    @2
    @5
    @10
    cA
    cB
    xaddge0
    an4s
    @7
    elxrge0
    sylanbrc
    syl2anb
end
