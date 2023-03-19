include "cupgr.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cdif.mm"
include "cnbgr.mm"
include "co.mm"
include "wceq.mm"
include "cpr.mm"
include "wss.mm"
include "cvtx.mm"
include "cfv.mm"
include "eqid.mm"
include "nbgrssovtx.mm"
include "difpr.mm"
include "upgrres1lem2.mm"
include "eqcomi.mm"
include "a1i.mm"
include "difeq1d.mm"
include "syl5eq.mm"
include "syl5sseqr.mm"
include "adantr.mm"
include "cv.mm"
include "wral.mm"
include "w3a.mm"
include "simpl.mm"
include "anim1i.mm"
include "df-3an.mm"
include "sylibr.mm"
include "wi.mm"
include "wne.mm"
include "dif32.mm"
include "eqtri.mm"
include "eleq2i.mm"
include "eldifsn.mm"
include "bitri.mm"
include "simplbi.mm"
include "eleq2.mm"
include "syl5ibr.mm"
include "adantl.mm"
include "imp.mm"
include "nbupgrres.mm"
include "sylc.mm"
include "ralrimiva.mm"
include "dfss3.mm"
include "eqssd.mm"
include "ex.mm"

theorem nbupgruvtxres
  let cS: class S
  let ve: setvar e
  let cE: class E
  let cF: class F
  let cG: class G
  let cK: class K
  let cN: class N
  let cV: class V
  let vn: setvar n
  assume nbupgruvtxres.v: |- V = ( Vtx ` G )
  assume nbupgruvtxres.e: |- E = ( Edg ` G )
  assume nbupgruvtxres.f: |- F = { e e. E | N e/ e }
  assume nbupgruvtxres.s: |- S = <. ( V \ { N } ) , ( _I |` F ) >.

  disjoint E e
  disjoint G e
  disjoint K e
  disjoint N e
  disjoint V e
  disjoint G n
  disjoint e n
  disjoint K n
  disjoint N n
  disjoint S n
  disjoint V n
  assert |- ( ( ( G e. UPGraph /\ N e. V ) /\ K e. ( V \ { N } ) ) -> ( ( G NeighbVtx K ) = ( V \ { K } ) -> ( S NeighbVtx K ) = ( V \ { N , K } ) ) )

  proof
    cG
    cupgr
    wcel
    cN
    cV
    wcel
    wa
    #
    cK
    cV
    cN
    csn
    #
    cdif
    #
    wcel
    #
    wa
    #
    cG
    cK
    cnbgr
    co
    #
    cV
    cK
    csn
    #
    cdif
    #
    wceq
    #
    cS
    cK
    cnbgr
    co
    #
    cV
    cN
    cK
    cpr
    cdif
    #
    wceq
    @4
    @8
    wa
    #
    @9
    @10
    @4
    @9
    @10
    wss
    @8
    @4
    cS
    cvtx
    cfv
    #
    @6
    cdif
    #
    @9
    @10
    cS
    @12
    cK
    @12
    eqid
    nbgrssovtx
    @4
    @10
    @2
    @6
    cdif
    #
    @13
    cV
    cN
    cK
    difpr
    #
    @4
    @2
    @12
    @6
    @2
    @12
    wceq
    @4
    @12
    @2
    cS
    ve
    cE
    cF
    cG
    cN
    cV
    nbupgruvtxres.v
    nbupgruvtxres.e
    nbupgruvtxres.f
    nbupgruvtxres.s
    upgrres1lem2
    eqcomi
    a1i
    difeq1d
    syl5eq
    syl5sseqr
    adantr
    @11
    vn
    cv
    #
    @9
    wcel
    #
    vn
    @10
    wral
    @10
    @9
    wss
    @11
    @17
    vn
    @10
    @11
    @16
    @10
    wcel
    #
    wa
    #
    @0
    @3
    @18
    w3a
    #
    @16
    @5
    wcel
    #
    @17
    @19
    @4
    @18
    wa
    @20
    @11
    @4
    @18
    @4
    @8
    simpl
    anim1i
    @0
    @3
    @18
    df-3an
    sylibr
    @11
    @18
    @21
    @8
    @18
    @21
    wi
    @4
    @18
    @21
    @8
    @16
    @7
    wcel
    #
    @18
    @22
    @16
    cN
    wne
    #
    @18
    @16
    @7
    @1
    cdif
    #
    wcel
    @22
    @23
    wa
    @10
    @24
    @16
    @10
    @14
    @24
    @15
    cV
    @1
    @6
    dif32
    eqtri
    eleq2i
    @16
    @7
    cN
    eldifsn
    bitri
    simplbi
    @5
    @7
    @16
    eleq2
    syl5ibr
    adantl
    imp
    cS
    ve
    cE
    cF
    cG
    cK
    @16
    cN
    cV
    nbupgruvtxres.v
    nbupgruvtxres.e
    nbupgruvtxres.f
    nbupgruvtxres.s
    nbupgrres
    sylc
    ralrimiva
    vn
    @10
    @9
    dfss3
    sylibr
    eqssd
    ex
end
