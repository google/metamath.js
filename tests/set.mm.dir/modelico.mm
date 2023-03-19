include "cr.mm"
include "wcel.mm"
include "crp.mm"
include "wa.mm"
include "cmo.mm"
include "co.mm"
include "cc0.mm"
include "cico.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "modcl.mm"
include "modge0.mm"
include "modlt.mm"
include "cxr.mm"
include "w3a.mm"
include "wb.mm"
include "0re.mm"
include "rpxr.mm"
include "adantl.mm"
include "elico2.mm"
include "sylancr.mm"
include "mpbir3and.mm"

theorem modelico
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR+ ) -> ( A mod B ) e. ( 0 [,) B ) )

  proof
    cA
    cr
    wcel
    #
    cB
    crp
    wcel
    #
    wa
    #
    cA
    cB
    cmo
    co
    #
    cc0
    cB
    cico
    co
    wcel
    #
    @3
    cr
    wcel
    #
    cc0
    @3
    cle
    wbr
    #
    @3
    cB
    clt
    wbr
    #
    cA
    cB
    modcl
    cA
    cB
    modge0
    cA
    cB
    modlt
    @2
    cc0
    cr
    wcel
    cB
    cxr
    wcel
    #
    @4
    @5
    @6
    @7
    w3a
    wb
    0re
    @1
    @8
    @0
    cB
    rpxr
    adantl
    cc0
    cB
    @3
    elico2
    sylancr
    mpbir3and
end
