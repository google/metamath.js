include "cxr.mm"
include "wcel.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "xrleid.mm"
include "ad2antlr.mm"
include "wceq.mm"
include "iftrue.mm"
include "adantl.mm"
include "breqtrrd.mm"
include "wn.mm"
include "xrletri.mm"
include "orcanai.mm"
include "iffalse.mm"
include "pm2.61dan.mm"

theorem xrmax2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR* /\ B e. RR* ) -> B <_ if ( A <_ B , B , A ) )

  proof
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    wa
    #
    cA
    cB
    cle
    wbr
    #
    cB
    @3
    cB
    cA
    cif
    #
    cle
    wbr
    @2
    @3
    wa
    cB
    cB
    @4
    cle
    @1
    cB
    cB
    cle
    wbr
    @0
    @3
    cB
    xrleid
    ad2antlr
    @3
    @4
    cB
    wceq
    @2
    @3
    cB
    cA
    iftrue
    adantl
    breqtrrd
    @2
    @3
    wn
    #
    wa
    cB
    cA
    @4
    cle
    @2
    @3
    cB
    cA
    cle
    wbr
    cA
    cB
    xrletri
    orcanai
    @5
    @4
    cA
    wceq
    @2
    @3
    cB
    cA
    iffalse
    adantl
    breqtrrd
    pm2.61dan
end
