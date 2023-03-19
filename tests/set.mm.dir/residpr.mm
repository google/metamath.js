include "wcel.mm"
include "wa.mm"
include "cid.mm"
include "cpr.mm"
include "cres.mm"
include "csn.mm"
include "cun.mm"
include "cop.mm"
include "df-pr.mm"
include "reseq2i.mm"
include "resundi.mm"
include "eqtri.mm"
include "cxp.mm"
include "wceq.mm"
include "xpsng.mm"
include "anidms.mm"
include "adantr.mm"
include "adantl.mm"
include "uneq12d.mm"
include "restidsing.mm"
include "uneq12i.mm"
include "3eqtr4g.mm"
include "syl5eq.mm"

theorem residpr
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ B e. W ) -> ( _I |` { A , B } ) = { <. A , A >. , <. B , B >. } )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    wa
    #
    cid
    cA
    cB
    cpr
    #
    cres
    #
    cid
    cA
    csn
    #
    cres
    #
    cid
    cB
    csn
    #
    cres
    #
    cun
    #
    cA
    cA
    cop
    #
    cB
    cB
    cop
    #
    cpr
    #
    @4
    cid
    @5
    @7
    cun
    #
    cres
    @9
    @3
    @13
    cid
    cA
    cB
    df-pr
    reseq2i
    cid
    @5
    @7
    resundi
    eqtri
    @2
    @5
    @5
    cxp
    #
    @7
    @7
    cxp
    #
    cun
    @10
    csn
    #
    @11
    csn
    #
    cun
    @9
    @12
    @2
    @14
    @16
    @15
    @17
    @0
    @14
    @16
    wceq
    #
    @1
    @0
    @18
    cA
    cA
    cV
    cV
    xpsng
    anidms
    adantr
    @1
    @15
    @17
    wceq
    #
    @0
    @1
    @19
    cB
    cB
    cW
    cW
    xpsng
    anidms
    adantl
    uneq12d
    @6
    @14
    @8
    @15
    cA
    restidsing
    cB
    restidsing
    uneq12i
    @10
    @11
    df-pr
    3eqtr4g
    syl5eq
end
