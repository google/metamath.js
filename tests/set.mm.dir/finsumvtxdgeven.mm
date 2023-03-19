include "cupgr.mm"
include "wcel.mm"
include "cfn.mm"
include "w3a.mm"
include "c2.mm"
include "chash.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "cv.mm"
include "csu.mm"
include "cdvds.mm"
include "cz.mm"
include "wceq.mm"
include "wbr.mm"
include "cn0.mm"
include "hashcl.mm"
include "3ad2ant3.mm"
include "nn0zd.mm"
include "eqidd.mm"
include "2teven.mm"
include "syl2anc.mm"
include "finsumvtxdg2size.mm"
include "breqtrrd.mm"

theorem finsumvtxdgeven
  let vv: setvar v
  let cD: class D
  let cG: class G
  let cI: class I
  let cV: class V
  assume finsumvtxdgeven.v: |- V = ( Vtx ` G )
  assume finsumvtxdgeven.i: |- I = ( iEdg ` G )
  assume finsumvtxdgeven.d: |- D = ( VtxDeg ` G )

  disjoint G v
  disjoint V v
  assert |- ( ( G e. UPGraph /\ V e. Fin /\ I e. Fin ) -> 2 || sum_ v e. V ( D ` v ) )

  proof
    cG
    cupgr
    wcel
    #
    cV
    cfn
    wcel
    #
    cI
    cfn
    wcel
    #
    w3a
    #
    c2
    c2
    cI
    chash
    cfv
    #
    cmul
    co
    #
    cV
    vv
    cv
    cD
    cfv
    vv
    csu
    cdvds
    @3
    @4
    cz
    wcel
    @5
    @5
    wceq
    c2
    @5
    cdvds
    wbr
    @3
    @4
    @2
    @0
    @4
    cn0
    wcel
    @1
    cI
    hashcl
    3ad2ant3
    nn0zd
    @3
    @5
    eqidd
    @4
    @5
    2teven
    syl2anc
    vv
    cD
    cG
    cI
    cV
    finsumvtxdgeven.v
    finsumvtxdgeven.i
    finsumvtxdgeven.d
    finsumvtxdg2size
    breqtrrd
end
