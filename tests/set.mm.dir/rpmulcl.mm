include "crp.mm"
include "wcel.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "cr.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "rpre.mm"
include "remulcl.mm"
include "syl2an.mm"
include "elrp.mm"
include "mulgt0.mm"
include "syl2anb.mm"
include "sylanbrc.mm"

theorem rpmulcl
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR+ /\ B e. RR+ ) -> ( A x. B ) e. RR+ )

  proof
    cA
    crp
    wcel
    #
    cB
    crp
    wcel
    #
    wa
    cA
    cB
    cmul
    co
    #
    cr
    wcel
    #
    cc0
    @2
    clt
    wbr
    #
    @2
    crp
    wcel
    @0
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    @3
    @1
    cA
    rpre
    cB
    rpre
    cA
    cB
    remulcl
    syl2an
    @0
    @5
    cc0
    cA
    clt
    wbr
    wa
    @6
    cc0
    cB
    clt
    wbr
    wa
    @4
    @1
    cA
    elrp
    cB
    elrp
    cA
    cB
    mulgt0
    syl2anb
    @2
    elrp
    sylanbrc
end
