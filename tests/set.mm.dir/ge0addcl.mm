include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "wcel.mm"
include "cr.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "caddc.mm"
include "elrege0.mm"
include "readdcl.mm"
include "ad2ant2r.mm"
include "addge0.mm"
include "an4s.mm"
include "sylanbrc.mm"
include "syl2anb.mm"

theorem ge0addcl
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ( 0 [,) +oo ) /\ B e. ( 0 [,) +oo ) ) -> ( A + B ) e. ( 0 [,) +oo ) )

  proof
    cA
    cc0
    cpnf
    cico
    co
    #
    wcel
    cA
    cr
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
    cr
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
    caddc
    co
    #
    @0
    wcel
    #
    cB
    @0
    wcel
    cA
    elrege0
    cB
    elrege0
    @3
    @6
    wa
    @7
    cr
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
    readdcl
    ad2ant2r
    @1
    @4
    @2
    @5
    @10
    cA
    cB
    addge0
    an4s
    @7
    elrege0
    sylanbrc
    syl2anb
end
