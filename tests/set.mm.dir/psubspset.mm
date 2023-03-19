include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "wss.mm"
include "co.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "cab.mm"
include "wceq.mm"
include "elex.mm"
include "cpsubsp.mm"
include "cfv.mm"
include "catm.mm"
include "cjn.mm"
include "cple.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "sseq2d.mm"
include "oveqd.mm"
include "breq2d.mm"
include "breqd.mm"
include "bitrd.mm"
include "imbi1d.mm"
include "raleqbidv.mm"
include "2ralbidv.mm"
include "anbi12d.mm"
include "abbidv.mm"
include "df-psubsp.mm"
include "cpw.mm"
include "fvex.mm"
include "eqeltri.mm"
include "pwex.mm"
include "selpw.mm"
include "anbi1i.mm"
include "abbii.mm"
include "ssab2.mm"
include "eqsstr3i.mm"
include "ssexi.mm"
include "fvmpt.mm"
include "syl5eq.mm"
include "syl.mm"

theorem psubspset
  let cA: class A
  let cB: class B
  let cS: class S
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let vs: setvar s
  let vr: setvar r
  let vq: setvar q
  let vp: setvar p
  let vk: setvar k
  assume psubspset.l: |- .<_ = ( le ` K )
  assume psubspset.j: |- .\/ = ( join ` K )
  assume psubspset.a: |- A = ( Atoms ` K )
  assume psubspset.s: |- S = ( PSubSp ` K )

  disjoint r s
  disjoint A r
  disjoint A s
  disjoint p q
  disjoint p r
  disjoint p s
  disjoint K p
  disjoint q r
  disjoint q s
  disjoint K q
  disjoint K r
  disjoint K s
  disjoint k r
  disjoint k s
  disjoint A k
  disjoint k p
  disjoint k q
  disjoint K k
  disjoint .\/ k
  disjoint .<_ k
  assert |- ( K e. B -> S = { s | ( s C_ A /\ A. p e. s A. q e. s A. r e. A ( r .<_ ( p .\/ q ) -> r e. s ) ) } )

  proof
    cK
    cB
    wcel
    cK
    cvv
    wcel
    #
    cS
    vs
    cv
    #
    cA
    wss
    #
    vr
    cv
    #
    vp
    cv
    #
    vq
    cv
    #
    c.or
    co
    #
    c.le
    wbr
    #
    @3
    @1
    wcel
    #
    wi
    #
    vr
    cA
    wral
    #
    vq
    @1
    wral
    vp
    @1
    wral
    #
    wa
    #
    vs
    cab
    #
    wceq
    cK
    cB
    elex
    @0
    cS
    cK
    cpsubsp
    cfv
    @13
    psubspset.s
    vk
    cK
    @1
    vk
    cv
    #
    catm
    cfv
    #
    wss
    #
    @3
    @4
    @5
    @14
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
    @8
    wi
    #
    vr
    @15
    wral
    #
    vq
    @1
    wral
    vp
    @1
    wral
    #
    wa
    #
    vs
    cab
    @13
    cvv
    cpsubsp
    @14
    cK
    wceq
    #
    @24
    @12
    vs
    @25
    @16
    @2
    @23
    @11
    @25
    @15
    cA
    @1
    @25
    @15
    cK
    catm
    cfv
    #
    cA
    @14
    cK
    catm
    fveq2
    psubspset.a
    syl6eqr
    #
    sseq2d
    @25
    @22
    @10
    vp
    vq
    @1
    @1
    @25
    @21
    @9
    vr
    @15
    cA
    @27
    @25
    @20
    @7
    @8
    @25
    @20
    @3
    @6
    @19
    wbr
    @7
    @25
    @18
    @6
    @3
    @19
    @25
    @17
    c.or
    @4
    @5
    @25
    @17
    cK
    cjn
    cfv
    c.or
    @14
    cK
    cjn
    fveq2
    psubspset.j
    syl6eqr
    oveqd
    breq2d
    @25
    @19
    c.le
    @3
    @6
    @25
    @19
    cK
    cple
    cfv
    c.le
    @14
    cK
    cple
    fveq2
    psubspset.l
    syl6eqr
    breqd
    bitrd
    imbi1d
    raleqbidv
    2ralbidv
    anbi12d
    abbidv
    vk
    vs
    vr
    vq
    vp
    df-psubsp
    @13
    cA
    cpw
    #
    cA
    cA
    @26
    cvv
    psubspset.a
    cK
    catm
    fvex
    eqeltri
    pwex
    @13
    @1
    @28
    wcel
    #
    @11
    wa
    #
    vs
    cab
    @28
    @30
    @12
    vs
    @29
    @2
    @11
    vs
    cA
    selpw
    anbi1i
    abbii
    @11
    vs
    @28
    ssab2
    eqsstr3i
    ssexi
    fvmpt
    syl5eq
    syl
end
