include "crp.mm"
include "wcel.mm"
include "wa.mm"
include "cdiv.mm"
include "co.mm"
include "cr.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wne.mm"
include "rpre.mm"
include "rprene0.mm"
include "redivcl.mm"
include "3expb.mm"
include "syl2an.mm"
include "elrp.mm"
include "divgt0.mm"
include "syl2anb.mm"
include "sylanbrc.mm"

theorem rpdivcl
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR+ /\ B e. RR+ ) -> ( A / B ) e. RR+ )

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
    cdiv
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
    cB
    cc0
    wne
    #
    wa
    @3
    @1
    cA
    rpre
    cB
    rprene0
    @5
    @6
    @7
    @3
    cA
    cB
    redivcl
    3expb
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
    divgt0
    syl2anb
    @2
    elrp
    sylanbrc
end
