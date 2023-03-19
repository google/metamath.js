include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "wne.mm"
include "co.mm"
include "wbr.mm"
include "crab.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "cab.mm"
include "elex.mm"
include "clines.mm"
include "cfv.mm"
include "cjn.mm"
include "cple.mm"
include "catm.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "breqd.mm"
include "oveqd.mm"
include "breq2d.mm"
include "bitrd.mm"
include "rabeqbidv.mm"
include "eqeq2d.mm"
include "anbi2d.mm"
include "rexeqbidv.mm"
include "abbidv.mm"
include "df-lines.mm"
include "fvex.mm"
include "eqeltri.mm"
include "csn.mm"
include "df-sn.mm"
include "snex.mm"
include "eqeltrri.mm"
include "simpr.mm"
include "ss2abi.mm"
include "ssexi.mm"
include "ab2rexex2.mm"
include "fvmpt.mm"
include "syl5eq.mm"
include "syl.mm"

theorem lineset
  let cA: class A
  let cB: class B
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cN: class N
  let vs: setvar s
  let vr: setvar r
  let vq: setvar q
  let vp: setvar p
  let vk: setvar k
  assume lineset.l: |- .<_ = ( le ` K )
  assume lineset.j: |- .\/ = ( join ` K )
  assume lineset.a: |- A = ( Atoms ` K )
  assume lineset.n: |- N = ( Lines ` K )

  disjoint p q
  disjoint p r
  disjoint p s
  disjoint A p
  disjoint q r
  disjoint q s
  disjoint A q
  disjoint r s
  disjoint A r
  disjoint A s
  disjoint K p
  disjoint K q
  disjoint K r
  disjoint K s
  disjoint .\/ s
  disjoint .<_ s
  disjoint k p
  disjoint k q
  disjoint k r
  disjoint k s
  disjoint A k
  disjoint K k
  disjoint .\/ k
  disjoint .<_ k
  assert |- ( K e. B -> N = { s | E. q e. A E. r e. A ( q =/= r /\ s = { p e. A | p .<_ ( q .\/ r ) } ) } )

  proof
    cK
    cB
    wcel
    cK
    cvv
    wcel
    #
    cN
    vq
    cv
    #
    vr
    cv
    #
    wne
    #
    vs
    cv
    #
    vp
    cv
    #
    @1
    @2
    c.or
    co
    #
    c.le
    wbr
    #
    vp
    cA
    crab
    #
    wceq
    #
    wa
    #
    vr
    cA
    wrex
    #
    vq
    cA
    wrex
    #
    vs
    cab
    #
    wceq
    cK
    cB
    elex
    @0
    cN
    cK
    clines
    cfv
    @13
    lineset.n
    vk
    cK
    @3
    @4
    @5
    @1
    @2
    vk
    cv
    #
    cjn
    cfv
    #
    co
    #
    @14
    cple
    cfv
    #
    wbr
    #
    vp
    @14
    catm
    cfv
    #
    crab
    #
    wceq
    #
    wa
    #
    vr
    @19
    wrex
    #
    vq
    @19
    wrex
    #
    vs
    cab
    @13
    cvv
    clines
    @14
    cK
    wceq
    #
    @24
    @12
    vs
    @25
    @23
    @11
    vq
    @19
    cA
    @25
    @19
    cK
    catm
    cfv
    #
    cA
    @14
    cK
    catm
    fveq2
    lineset.a
    syl6eqr
    #
    @25
    @22
    @10
    vr
    @19
    cA
    @27
    @25
    @21
    @9
    @3
    @25
    @20
    @8
    @4
    @25
    @18
    @7
    vp
    @19
    cA
    @27
    @25
    @18
    @5
    @16
    c.le
    wbr
    @7
    @25
    @17
    c.le
    @5
    @16
    @25
    @17
    cK
    cple
    cfv
    c.le
    @14
    cK
    cple
    fveq2
    lineset.l
    syl6eqr
    breqd
    @25
    @16
    @6
    @5
    c.le
    @25
    @15
    c.or
    @1
    @2
    @25
    @15
    cK
    cjn
    cfv
    c.or
    @14
    cK
    cjn
    fveq2
    lineset.j
    syl6eqr
    oveqd
    breq2d
    bitrd
    rabeqbidv
    eqeq2d
    anbi2d
    rexeqbidv
    rexeqbidv
    abbidv
    vk
    vs
    vr
    vq
    vp
    df-lines
    @10
    vq
    vr
    vs
    cA
    cA
    cA
    @26
    cvv
    lineset.a
    cK
    catm
    fvex
    eqeltri
    #
    @28
    @10
    vs
    cab
    @9
    vs
    cab
    #
    @8
    csn
    @29
    cvv
    vs
    @8
    df-sn
    @8
    snex
    eqeltrri
    @10
    @9
    vs
    @3
    @9
    simpr
    ss2abi
    ssexi
    ab2rexex2
    fvmpt
    syl5eq
    syl
end
