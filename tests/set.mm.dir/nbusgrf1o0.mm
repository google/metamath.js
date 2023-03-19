include "cusgr.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cpr.mm"
include "wral.mm"
include "wceq.mm"
include "wreu.mm"
include "wf1o.mm"
include "cnbgr.mm"
include "co.mm"
include "eleq2i.mm"
include "wb.mm"
include "nbusgreledg.mm"
include "adantr.mm"
include "prcom.mm"
include "eleq1i.mm"
include "biimpi.mm"
include "adantl.mm"
include "prid1g.mm"
include "crab.mm"
include "eleq2.mm"
include "elrab.mm"
include "bitri.mm"
include "sylanbrc.mm"
include "ex.mm"
include "sylbid.mm"
include "syl5bi.mm"
include "imp.mm"
include "ralrimiva.mm"
include "rabeq2i.mm"
include "edgnbusgreu.mm"
include "sylan2b.mm"
include "f1ompt.mm"

theorem nbusgrf1o0
  let cU: class U
  let ve: setvar e
  let vn: setvar n
  let cE: class E
  let cF: class F
  let cG: class G
  let cI: class I
  let cN: class N
  let cV: class V
  let vi: setvar i
  let cM: class M
  assume nbusgrf1o1.v: |- V = ( Vtx ` G )
  assume nbusgrf1o1.e: |- E = ( Edg ` G )
  assume nbusgrf1o1.n: |- N = ( G NeighbVtx U )
  assume nbusgrf1o1.i: |- I = { e e. E | U e. e }
  assume nbusgrf1o.f: |- F = ( n e. N |-> { U , n } )

  disjoint F e
  disjoint E e
  disjoint U e
  disjoint E n
  disjoint G e
  disjoint G n
  disjoint e n
  disjoint I e
  disjoint I n
  disjoint N e
  disjoint N n
  disjoint U n
  disjoint V e
  disjoint V n
  disjoint E i
  disjoint e i
  disjoint G i
  disjoint M i
  disjoint N i
  disjoint U i
  disjoint V i
  assert |- ( ( G e. USGraph /\ U e. V ) -> F : N -1-1-onto-> I )

  proof
    cG
    cusgr
    wcel
    #
    cU
    cV
    wcel
    #
    wa
    #
    cU
    vn
    cv
    #
    cpr
    #
    cI
    wcel
    #
    vn
    cN
    wral
    ve
    cv
    #
    @4
    wceq
    vn
    cN
    wreu
    #
    ve
    cI
    wral
    cN
    cI
    cF
    wf1o
    @2
    @5
    vn
    cN
    @2
    @3
    cN
    wcel
    #
    @5
    @8
    @3
    cG
    cU
    cnbgr
    co
    #
    wcel
    #
    @2
    @5
    cN
    @9
    @3
    nbusgrf1o1.n
    eleq2i
    @2
    @10
    @3
    cU
    cpr
    #
    cE
    wcel
    #
    @5
    @0
    @10
    @12
    wb
    @1
    cE
    cG
    cU
    @3
    nbusgrf1o1.e
    nbusgreledg
    adantr
    @2
    @12
    @5
    @2
    @12
    wa
    @4
    cE
    wcel
    #
    cU
    @4
    wcel
    #
    @5
    @12
    @13
    @2
    @12
    @13
    @11
    @4
    cE
    @3
    cU
    prcom
    eleq1i
    biimpi
    adantl
    @2
    @14
    @12
    @1
    @14
    @0
    cU
    @3
    cV
    prid1g
    adantl
    adantr
    @5
    @4
    cU
    @6
    wcel
    #
    ve
    cE
    crab
    #
    wcel
    @13
    @14
    wa
    cI
    @16
    @4
    nbusgrf1o1.i
    eleq2i
    @15
    @14
    ve
    @4
    cE
    @6
    @4
    cU
    eleq2
    elrab
    bitri
    sylanbrc
    ex
    sylbid
    syl5bi
    imp
    ralrimiva
    @2
    @7
    ve
    cI
    @6
    cI
    wcel
    @2
    @6
    cE
    wcel
    @15
    wa
    @7
    @15
    ve
    cI
    cE
    nbusgrf1o1.i
    rabeq2i
    @6
    vn
    cE
    cG
    cU
    cN
    cV
    nbusgrf1o1.v
    nbusgrf1o1.e
    nbusgrf1o1.n
    edgnbusgreu
    sylan2b
    ralrimiva
    vn
    ve
    cN
    cI
    @4
    cF
    nbusgrf1o.f
    f1ompt
    sylanbrc
end
