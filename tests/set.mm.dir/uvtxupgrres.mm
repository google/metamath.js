include "cuvtx.mm"
include "cfv.mm"
include "wcel.mm"
include "cnbgr.mm"
include "co.mm"
include "csn.mm"
include "cdif.mm"
include "wceq.mm"
include "cupgr.mm"
include "wa.mm"
include "uvtxnbgr.mm"
include "cvtx.mm"
include "cpr.mm"
include "nbupgruvtxres.mm"
include "imp.mm"
include "upgrres1lem2.mm"
include "difeq1i.mm"
include "a1i.mm"
include "difpr.mm"
include "syl6reqr.mm"
include "adantr.mm"
include "eqtrd.mm"
include "wb.mm"
include "simpr.mm"
include "syl6eleqr.mm"
include "eqid.mm"
include "uvtxnbgrb.mm"
include "syl.mm"
include "mpbird.mm"
include "ex.mm"
include "syl5.mm"

theorem uvtxupgrres
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
  assert |- ( ( ( G e. UPGraph /\ N e. V ) /\ K e. ( V \ { N } ) ) -> ( K e. ( UnivVtx ` G ) -> K e. ( UnivVtx ` S ) ) )

  proof
    cK
    cG
    cuvtx
    cfv
    wcel
    cG
    cK
    cnbgr
    co
    cV
    cK
    csn
    #
    cdif
    wceq
    #
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
    cdif
    #
    wcel
    #
    wa
    #
    cK
    cS
    cuvtx
    cfv
    wcel
    #
    cG
    cK
    cV
    nbupgruvtxres.v
    uvtxnbgr
    @5
    @1
    @6
    @5
    @1
    wa
    #
    @6
    cS
    cK
    cnbgr
    co
    #
    cS
    cvtx
    cfv
    #
    @0
    cdif
    #
    wceq
    #
    @7
    @8
    cV
    cN
    cK
    cpr
    cdif
    #
    @10
    @5
    @1
    @8
    @12
    wceq
    cS
    ve
    cE
    cF
    cG
    cK
    cN
    cV
    nbupgruvtxres.v
    nbupgruvtxres.e
    nbupgruvtxres.f
    nbupgruvtxres.s
    nbupgruvtxres
    imp
    @5
    @12
    @10
    wceq
    @1
    @5
    @10
    @3
    @0
    cdif
    #
    @12
    @10
    @13
    wceq
    @5
    @9
    @3
    @0
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
    #
    difeq1i
    a1i
    cV
    cN
    cK
    difpr
    syl6reqr
    adantr
    eqtrd
    @7
    cK
    @9
    wcel
    #
    @6
    @11
    wb
    @5
    @15
    @1
    @5
    cK
    @3
    @9
    @2
    @4
    simpr
    @14
    syl6eleqr
    adantr
    cS
    cK
    @9
    @9
    eqid
    uvtxnbgrb
    syl
    mpbird
    ex
    syl5
end
