include "crp.mm"
include "wcel.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "cr.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "rpre.mm"
include "readdcl.mm"
include "syl2an.mm"
include "elrp.mm"
include "addgt0.mm"
include "an4s.mm"
include "syl2anb.mm"
include "sylanbrc.mm"

theorem rpaddcl
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR+ /\ B e. RR+ ) -> ( A + B ) e. RR+ )

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
    caddc
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
    readdcl
    syl2an
    @0
    @5
    cc0
    cA
    clt
    wbr
    #
    wa
    @6
    cc0
    cB
    clt
    wbr
    #
    wa
    @4
    @1
    cA
    elrp
    cB
    elrp
    @5
    @6
    @7
    @8
    @4
    cA
    cB
    addgt0
    an4s
    syl2anb
    @2
    elrp
    sylanbrc
end
