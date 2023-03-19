include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wcel.mm"
include "cxr.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cxmu.mm"
include "elxrge0.mm"
include "xmulcl.mm"
include "ad2ant2r.mm"
include "xmulge0.mm"
include "sylanbrc.mm"
include "syl2anb.mm"

theorem ge0xmulcl
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ( 0 [,] +oo ) /\ B e. ( 0 [,] +oo ) ) -> ( A *e B ) e. ( 0 [,] +oo ) )

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
    cxmu
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
    @8
    @1
    @4
    @9
    @2
    @5
    cA
    cB
    xmulcl
    ad2ant2r
    cA
    cB
    xmulge0
    @7
    elxrge0
    sylanbrc
    syl2anb
end
