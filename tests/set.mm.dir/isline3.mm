include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cv.mm"
include "wne.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "clat.mm"
include "wb.mm"
include "hllat.mm"
include "adantr.mm"
include "isline2.mm"
include "syl.mm"
include "simpll.mm"
include "simplr.mm"
include "ad2antrr.mm"
include "atbase.mm"
include "ad2antrl.mm"
include "ad2antll.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "pmap11.mm"
include "anbi2d.mm"
include "2rexbidva.mm"
include "bitrd.mm"

theorem isline3
  let cA: class A
  let cB: class B
  let c.or: class .\/
  let cK: class K
  let cM: class M
  let cN: class N
  let cX: class X
  let vq: setvar q
  let vp: setvar p
  assume isline3.b: |- B = ( Base ` K )
  assume isline3.j: |- .\/ = ( join ` K )
  assume isline3.a: |- A = ( Atoms ` K )
  assume isline3.n: |- N = ( Lines ` K )
  assume isline3.m: |- M = ( pmap ` K )

  disjoint p q
  disjoint B p
  disjoint B q
  disjoint A p
  disjoint A q
  disjoint K p
  disjoint K q
  disjoint M p
  disjoint M q
  disjoint X p
  disjoint X q
  assert |- ( ( K e. HL /\ X e. B ) -> ( ( M ` X ) e. N <-> E. p e. A E. q e. A ( p =/= q /\ X = ( p .\/ q ) ) ) )

  proof
    cK
    chlt
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    #
    cX
    cM
    cfv
    #
    cN
    wcel
    #
    vp
    cv
    #
    vq
    cv
    #
    wne
    #
    @3
    @5
    @6
    c.or
    co
    #
    cM
    cfv
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
    #
    @7
    cX
    @8
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
    @2
    cK
    clat
    wcel
    #
    @4
    @11
    wb
    @0
    @14
    @1
    cK
    hllat
    #
    adantr
    cA
    c.or
    cK
    cM
    cN
    @3
    vq
    vp
    isline3.j
    isline3.a
    isline3.n
    isline3.m
    isline2
    syl
    @2
    @10
    @13
    vp
    vq
    cA
    cA
    @2
    @5
    cA
    wcel
    #
    @6
    cA
    wcel
    #
    wa
    #
    wa
    #
    @9
    @12
    @7
    @19
    @0
    @1
    @8
    cB
    wcel
    #
    @9
    @12
    wb
    @0
    @1
    @18
    simpll
    @0
    @1
    @18
    simplr
    @19
    @14
    @5
    cB
    wcel
    #
    @6
    cB
    wcel
    #
    @20
    @0
    @14
    @1
    @18
    @15
    ad2antrr
    @16
    @21
    @2
    @17
    cA
    cB
    @5
    cK
    isline3.b
    isline3.a
    atbase
    ad2antrl
    @17
    @22
    @2
    @16
    cA
    cB
    @6
    cK
    isline3.b
    isline3.a
    atbase
    ad2antll
    cB
    c.or
    cK
    @5
    @6
    isline3.b
    isline3.j
    latjcl
    syl3anc
    cB
    cK
    cM
    cX
    @8
    isline3.b
    isline3.m
    pmap11
    syl3anc
    anbi2d
    2rexbidva
    bitrd
end
