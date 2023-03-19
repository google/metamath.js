include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wne.mm"
include "w3a.mm"
include "isltrn.mm"
include "3simpa.mm"
include "imim1i.mm"
include "3anass.mm"
include "3anrot.mm"
include "df-ne.mm"
include "anbi1i.mm"
include "3bitr3i.mm"
include "imbi1i.mm"
include "impexp.mm"
include "bitri.mm"
include "id.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "oveq1d.mm"
include "a1d.mm"
include "pm2.61.mm"
include "ax-mp.mm"
include "sylbi.mm"
include "impbii.mm"
include "2ralbii.mm"
include "anbi2i.mm"
include "syl6bb.mm"

theorem isltrn2N
  let cA: class A
  let cB: class B
  let cD: class D
  let cT: class T
  let cF: class F
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let vq: setvar q
  let vp: setvar p
  let vk: setvar k
  let vf: setvar f
  let vw: setvar w
  assume ltrnset.l: |- .<_ = ( le ` K )
  assume ltrnset.j: |- .\/ = ( join ` K )
  assume ltrnset.m: |- ./\ = ( meet ` K )
  assume ltrnset.a: |- A = ( Atoms ` K )
  assume ltrnset.h: |- H = ( LHyp ` K )
  assume ltrnset.d: |- D = ( ( LDil ` K ) ` W )
  assume ltrnset.t: |- T = ( ( LTrn ` K ) ` W )

  disjoint p q
  disjoint A p
  disjoint A q
  disjoint K p
  disjoint K q
  disjoint W p
  disjoint W q
  disjoint F p
  disjoint F q
  disjoint k p
  disjoint k q
  disjoint A k
  disjoint f k
  disjoint D f
  disjoint D k
  disjoint k w
  disjoint H k
  disjoint H w
  disjoint .\/ k
  disjoint f p
  disjoint f q
  disjoint f w
  disjoint K f
  disjoint K k
  disjoint p w
  disjoint q w
  disjoint K w
  disjoint .<_ k
  disjoint ./\ k
  disjoint A w
  disjoint D w
  disjoint .\/ w
  disjoint .<_ w
  disjoint ./\ w
  disjoint W f
  disjoint W w
  disjoint A f
  disjoint F f
  disjoint .\/ f
  disjoint .<_ f
  disjoint ./\ f
  assert |- ( ( K e. B /\ W e. H ) -> ( F e. T <-> ( F e. D /\ A. p e. A A. q e. A ( ( -. p .<_ W /\ -. q .<_ W /\ p =/= q ) -> ( ( p .\/ ( F ` p ) ) ./\ W ) = ( ( q .\/ ( F ` q ) ) ./\ W ) ) ) ) )

  proof
    cK
    cB
    wcel
    cW
    cH
    wcel
    wa
    cF
    cT
    wcel
    cF
    cD
    wcel
    #
    vp
    cv
    #
    cW
    c.le
    wbr
    wn
    #
    vq
    cv
    #
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    @1
    @1
    cF
    cfv
    #
    c.or
    co
    #
    cW
    c.an
    co
    @3
    @3
    cF
    cfv
    #
    c.or
    co
    #
    cW
    c.an
    co
    wceq
    #
    wi
    #
    vq
    cA
    wral
    vp
    cA
    wral
    #
    wa
    @0
    @2
    @4
    @1
    @3
    wne
    #
    w3a
    #
    @10
    wi
    #
    vq
    cA
    wral
    vp
    cA
    wral
    #
    wa
    cA
    cB
    cD
    cT
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cW
    vq
    vp
    ltrnset.l
    ltrnset.j
    ltrnset.m
    ltrnset.a
    ltrnset.h
    ltrnset.d
    ltrnset.t
    isltrn
    @12
    @16
    @0
    @11
    @15
    vp
    vq
    cA
    cA
    @11
    @15
    @14
    @5
    @10
    @2
    @4
    @13
    3simpa
    imim1i
    @15
    @1
    @3
    wceq
    #
    wn
    #
    @11
    wi
    #
    @11
    @15
    @18
    @5
    wa
    #
    @10
    wi
    @19
    @14
    @20
    @10
    @13
    @2
    @4
    w3a
    @13
    @5
    wa
    @14
    @20
    @13
    @2
    @4
    3anass
    @13
    @2
    @4
    3anrot
    @13
    @18
    @5
    @1
    @3
    df-ne
    anbi1i
    3bitr3i
    imbi1i
    @18
    @5
    @10
    impexp
    bitri
    @17
    @11
    wi
    @19
    @11
    wi
    @17
    @10
    @5
    @17
    @7
    @9
    cW
    c.an
    @17
    @1
    @3
    @6
    @8
    c.or
    @17
    id
    @1
    @3
    cF
    fveq2
    oveq12d
    oveq1d
    a1d
    @17
    @11
    pm2.61
    ax-mp
    sylbi
    impbii
    2ralbii
    anbi2i
    syl6bb
end
