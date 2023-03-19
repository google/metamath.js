include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cv.mm"
include "wne.mm"
include "cjn.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "wbr.mm"
include "eqid.mm"
include "isline3.mm"
include "cple.mm"
include "wn.mm"
include "wb.mm"
include "simpll.mm"
include "atbase.mm"
include "adantl.mm"
include "simplr.mm"
include "cvrval3.mm"
include "syl3anc.mm"
include "cal.mm"
include "hlatl.mm"
include "ad3antrrr.mm"
include "simpr.mm"
include "atncmp.mm"
include "necom.mm"
include "syl6bb.mm"
include "eqcom.mm"
include "a1i.mm"
include "anbi12d.mm"
include "rexbidva.mm"
include "bitrd.mm"
include "bitr4d.mm"

theorem isline4N
  let cA: class A
  let cB: class B
  let cC: class C
  let cK: class K
  let cM: class M
  let cN: class N
  let cX: class X
  let vp: setvar p
  let vq: setvar q
  assume isline4.b: |- B = ( Base ` K )
  assume isline4.c: |- C = ( <o ` K )
  assume isline4.a: |- A = ( Atoms ` K )
  assume isline4.n: |- N = ( Lines ` K )
  assume isline4.m: |- M = ( pmap ` K )

  disjoint A p
  disjoint B p
  disjoint K p
  disjoint M p
  disjoint X p
  disjoint p q
  disjoint A q
  disjoint B q
  disjoint C q
  disjoint K q
  disjoint M q
  disjoint X q
  assert |- ( ( K e. HL /\ X e. B ) -> ( ( M ` X ) e. N <-> E. p e. A p C X ) )

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
    @3
    @4
    cK
    cjn
    cfv
    #
    co
    #
    wceq
    #
    wa
    #
    vq
    cA
    wrex
    #
    vp
    cA
    wrex
    @3
    cX
    cC
    wbr
    #
    vp
    cA
    wrex
    cA
    cB
    @6
    cK
    cM
    cN
    cX
    vq
    vp
    isline4.b
    @6
    eqid
    #
    isline4.a
    isline4.n
    isline4.m
    isline3
    @2
    @11
    @10
    vp
    cA
    @2
    @3
    cA
    wcel
    #
    wa
    #
    @11
    @4
    @3
    cK
    cple
    cfv
    #
    wbr
    wn
    #
    @7
    cX
    wceq
    #
    wa
    #
    vq
    cA
    wrex
    #
    @10
    @14
    @0
    @3
    cB
    wcel
    #
    @1
    @11
    @19
    wb
    @0
    @1
    @13
    simpll
    @13
    @20
    @2
    cA
    cB
    @3
    cK
    isline4.b
    isline4.a
    atbase
    adantl
    @0
    @1
    @13
    simplr
    cA
    cB
    cC
    @6
    cK
    @15
    @3
    cX
    vq
    isline4.b
    @15
    eqid
    #
    @12
    isline4.c
    isline4.a
    cvrval3
    syl3anc
    @14
    @18
    @9
    vq
    cA
    @14
    @4
    cA
    wcel
    #
    wa
    #
    @16
    @5
    @17
    @8
    @23
    @16
    @4
    @3
    wne
    #
    @5
    @23
    cK
    cal
    wcel
    #
    @22
    @13
    @16
    @24
    wb
    @0
    @25
    @1
    @13
    @22
    cK
    hlatl
    ad3antrrr
    @14
    @22
    simpr
    @2
    @13
    @22
    simplr
    cA
    @4
    @3
    cK
    @15
    @21
    isline4.a
    atncmp
    syl3anc
    @4
    @3
    necom
    syl6bb
    @17
    @8
    wb
    @23
    @7
    cX
    eqcom
    a1i
    anbi12d
    rexbidva
    bitrd
    rexbidva
    bitr4d
end
