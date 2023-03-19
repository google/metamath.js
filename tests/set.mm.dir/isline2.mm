include "clat.mm"
include "wcel.mm"
include "cv.mm"
include "wne.mm"
include "co.mm"
include "cple.mm"
include "cfv.mm"
include "wbr.mm"
include "crab.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "eqid.mm"
include "isline.mm"
include "cbs.mm"
include "simpl.mm"
include "atbase.mm"
include "ad2antrl.mm"
include "ad2antll.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "pmapval.mm"
include "syldan.mm"
include "eqeq2d.mm"
include "anbi2d.mm"
include "2rexbidva.mm"
include "bitr4d.mm"

theorem isline2
  let cA: class A
  let c.or: class .\/
  let cK: class K
  let cM: class M
  let cN: class N
  let cX: class X
  let vq: setvar q
  let vp: setvar p
  let vr: setvar r
  assume isline2.j: |- .\/ = ( join ` K )
  assume isline2.a: |- A = ( Atoms ` K )
  assume isline2.n: |- N = ( Lines ` K )
  assume isline2.m: |- M = ( pmap ` K )

  disjoint p q
  disjoint A p
  disjoint A q
  disjoint K p
  disjoint K q
  disjoint X p
  disjoint X q
  disjoint p r
  disjoint q r
  disjoint A r
  disjoint .\/ r
  disjoint K r
  assert |- ( K e. Lat -> ( X e. N <-> E. p e. A E. q e. A ( p =/= q /\ X = ( M ` ( p .\/ q ) ) ) ) )

  proof
    cK
    clat
    wcel
    #
    cX
    cN
    wcel
    vp
    cv
    #
    vq
    cv
    #
    wne
    #
    cX
    vr
    cv
    @1
    @2
    c.or
    co
    #
    cK
    cple
    cfv
    #
    wbr
    vr
    cA
    crab
    #
    wceq
    #
    wa
    #
    vq
    cA
    wrex
    vp
    cA
    wrex
    @3
    cX
    @4
    cM
    cfv
    #
    wceq
    #
    wa
    #
    vq
    cA
    wrex
    vp
    cA
    wrex
    cA
    clat
    c.or
    cK
    @5
    cN
    cX
    vq
    vp
    vr
    @5
    eqid
    #
    isline2.j
    isline2.a
    isline2.n
    isline
    @0
    @11
    @8
    vp
    vq
    cA
    cA
    @0
    @1
    cA
    wcel
    #
    @2
    cA
    wcel
    #
    wa
    #
    wa
    #
    @10
    @7
    @3
    @16
    @9
    @6
    cX
    @0
    @15
    @4
    cK
    cbs
    cfv
    #
    wcel
    #
    @9
    @6
    wceq
    @16
    @0
    @1
    @17
    wcel
    #
    @2
    @17
    wcel
    #
    @18
    @0
    @15
    simpl
    @13
    @19
    @0
    @14
    cA
    @17
    @1
    cK
    @17
    eqid
    #
    isline2.a
    atbase
    ad2antrl
    @14
    @20
    @0
    @13
    cA
    @17
    @2
    cK
    @21
    isline2.a
    atbase
    ad2antll
    @17
    c.or
    cK
    @1
    @2
    @21
    isline2.j
    latjcl
    syl3anc
    cA
    @17
    clat
    cK
    @5
    cM
    @4
    vr
    @21
    @12
    isline2.a
    isline2.m
    pmapval
    syldan
    eqeq2d
    anbi2d
    2rexbidva
    bitr4d
end
