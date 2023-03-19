include "cxr.mm"
include "wcel.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "wceq.mm"
include "iftrue.mm"
include "adantl.mm"
include "xrleid.mm"
include "ad2antrr.mm"
include "eqbrtrd.mm"
include "wn.mm"
include "iffalse.mm"
include "xrletri.mm"
include "orcanai.mm"
include "pm2.61dan.mm"

theorem xrmin1
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR* /\ B e. RR* ) -> if ( A <_ B , A , B ) <_ A )

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
    @3
    cA
    cB
    cif
    #
    cA
    cle
    wbr
    @2
    @3
    wa
    @4
    cA
    cA
    cle
    @3
    @4
    cA
    wceq
    @2
    @3
    cA
    cB
    iftrue
    adantl
    @0
    cA
    cA
    cle
    wbr
    @1
    @3
    cA
    xrleid
    ad2antrr
    eqbrtrd
    @2
    @3
    wn
    #
    wa
    @4
    cB
    cA
    cle
    @5
    @4
    cB
    wceq
    @2
    @3
    cA
    cB
    iffalse
    adantl
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
    eqbrtrd
    pm2.61dan
end
