include "c2.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cpw.mm"
include "crab.mm"
include "wf.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "wceq.mm"
include "cxad.mm"
include "co.mm"
include "cc0.mm"
include "cvtxdg.mm"
include "fveq1i.mm"
include "vtxdgval.mm"
include "adantl.mm"
include "syl5eq.mm"
include "c0.mm"
include "eqid.mm"
include "lfgrnloop.mm"
include "adantr.mm"
include "fveq2d.mm"
include "hash0.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "cxr.mm"
include "cvv.mm"
include "cxnn0.mm"
include "ciedg.mm"
include "cdm.mm"
include "dmeqi.mm"
include "eqtri.mm"
include "fvex.mm"
include "dmex.mm"
include "eqeltri.mm"
include "rabex.mm"
include "hashxnn0.mm"
include "xnn0xr.mm"
include "mp2b.mm"
include "xaddid1.mm"
include "mp1i.mm"
include "3eqtrd.mm"

theorem vtxdlfgrval
  let vx: setvar x
  let cA: class A
  let cD: class D
  let cU: class U
  let cG: class G
  let cI: class I
  let cV: class V
  assume vtxdlfgrval.v: |- V = ( Vtx ` G )
  assume vtxdlfgrval.i: |- I = ( iEdg ` G )
  assume vtxdlfgrval.a: |- A = dom I
  assume vtxdlfgrval.d: |- D = ( VtxDeg ` G )

  disjoint A x
  disjoint G x
  disjoint I x
  disjoint U x
  disjoint V x
  assert |- ( ( I : A --> { x e. ~P V | 2 <_ ( # ` x ) } /\ U e. V ) -> ( D ` U ) = ( # ` { x e. A | U e. ( I ` x ) } ) )

  proof
    cA
    c2
    vx
    cv
    #
    chash
    cfv
    cle
    wbr
    vx
    cV
    cpw
    crab
    #
    cI
    wf
    #
    cU
    cV
    wcel
    #
    wa
    #
    cU
    cD
    cfv
    #
    cU
    @0
    cI
    cfv
    #
    wcel
    #
    vx
    cA
    crab
    #
    chash
    cfv
    #
    @6
    cU
    csn
    wceq
    vx
    cA
    crab
    #
    chash
    cfv
    #
    cxad
    co
    #
    @9
    cc0
    cxad
    co
    #
    @9
    @4
    @5
    cU
    cG
    cvtxdg
    cfv
    #
    cfv
    #
    @12
    cU
    cD
    @14
    vtxdlfgrval.d
    fveq1i
    @3
    @15
    @12
    wceq
    @2
    vx
    cA
    cU
    cG
    cI
    cV
    vtxdlfgrval.v
    vtxdlfgrval.i
    vtxdlfgrval.a
    vtxdgval
    adantl
    syl5eq
    @4
    @11
    cc0
    @9
    cxad
    @4
    @11
    c0
    chash
    cfv
    cc0
    @4
    @10
    c0
    chash
    @2
    @10
    c0
    wceq
    @3
    vx
    cA
    cU
    @1
    cG
    cI
    cV
    vtxdlfgrval.i
    vtxdlfgrval.a
    @1
    eqid
    lfgrnloop
    adantr
    fveq2d
    hash0
    syl6eq
    oveq2d
    @9
    cxr
    wcel
    #
    @13
    @9
    wceq
    @4
    @8
    cvv
    wcel
    @9
    cxnn0
    wcel
    @16
    @7
    vx
    cA
    cA
    cG
    ciedg
    cfv
    #
    cdm
    #
    cvv
    cA
    cI
    cdm
    @18
    vtxdlfgrval.a
    cI
    @17
    vtxdlfgrval.i
    dmeqi
    eqtri
    @17
    cG
    ciedg
    fvex
    dmex
    eqeltri
    rabex
    @8
    cvv
    hashxnn0
    @9
    xnn0xr
    mp2b
    @9
    xaddid1
    mp1i
    3eqtrd
end
