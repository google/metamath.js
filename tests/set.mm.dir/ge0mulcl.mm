include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "wcel.mm"
include "cr.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cmul.mm"
include "elrege0.mm"
include "remulcl.mm"
include "ad2ant2r.mm"
include "mulge0.mm"
include "sylanbrc.mm"
include "syl2anb.mm"

theorem ge0mulcl
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ( 0 [,) +oo ) /\ B e. ( 0 [,) +oo ) ) -> ( A x. B ) e. ( 0 [,) +oo ) )

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
    cmul
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
    @8
    @1
    @4
    @9
    @2
    @5
    cA
    cB
    remulcl
    ad2ant2r
    cA
    cB
    mulge0
    @7
    elrege0
    sylanbrc
    syl2anb
end
