include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "cbs.mm"
include "simp11.mm"
include "simp12.mm"
include "eqid.mm"
include "atbase.mm"
include "3ad2ant2.mm"
include "simp3.mm"
include "ltrnval1.mm"
include "syl112anc.mm"
include "simp13.mm"
include "eqtr4d.mm"
include "3expia.mm"
include "pm2.61.mm"
include "syl.mm"
include "re1tbw2.mm"
include "impbid1.mm"
include "ralbidva.mm"
include "ltrneq2.mm"
include "bitrd.mm"

theorem ltrneq
  let cA: class A
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let vp: setvar p
  assume ltrne.l: |- .<_ = ( le ` K )
  assume ltrne.a: |- A = ( Atoms ` K )
  assume ltrne.h: |- H = ( LHyp ` K )
  assume ltrne.t: |- T = ( ( LTrn ` K ) ` W )

  disjoint A p
  disjoint F p
  disjoint G p
  disjoint H p
  disjoint K p
  disjoint T p
  disjoint W p
  assert |- ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ G e. T ) -> ( A. p e. A ( -. p .<_ W -> ( F ` p ) = ( G ` p ) ) <-> F = G ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cF
    cT
    wcel
    #
    cG
    cT
    wcel
    #
    w3a
    #
    vp
    cv
    #
    cW
    c.le
    wbr
    #
    wn
    #
    @4
    cF
    cfv
    #
    @4
    cG
    cfv
    #
    wceq
    #
    wi
    #
    vp
    cA
    wral
    @9
    vp
    cA
    wral
    cF
    cG
    wceq
    @3
    @10
    @9
    vp
    cA
    @3
    @4
    cA
    wcel
    #
    wa
    #
    @10
    @9
    @12
    @5
    @9
    wi
    @10
    @9
    wi
    @3
    @11
    @5
    @9
    @3
    @11
    @5
    w3a
    #
    @7
    @4
    @8
    @13
    @0
    @1
    @4
    cK
    cbs
    cfv
    #
    wcel
    #
    @5
    @7
    @4
    wceq
    @0
    @1
    @2
    @11
    @5
    simp11
    #
    @0
    @1
    @2
    @11
    @5
    simp12
    @11
    @3
    @15
    @5
    cA
    @14
    @4
    cK
    @14
    eqid
    #
    ltrne.a
    atbase
    3ad2ant2
    #
    @3
    @11
    @5
    simp3
    #
    @14
    cT
    cF
    cH
    cK
    c.le
    chlt
    cW
    @4
    @17
    ltrne.l
    ltrne.h
    ltrne.t
    ltrnval1
    syl112anc
    @13
    @0
    @2
    @15
    @5
    @8
    @4
    wceq
    @16
    @0
    @1
    @2
    @11
    @5
    simp13
    @18
    @19
    @14
    cT
    cG
    cH
    cK
    c.le
    chlt
    cW
    @4
    @17
    ltrne.l
    ltrne.h
    ltrne.t
    ltrnval1
    syl112anc
    eqtr4d
    3expia
    @5
    @9
    pm2.61
    syl
    @9
    @6
    re1tbw2
    impbid1
    ralbidva
    cA
    cT
    cF
    cG
    cH
    cK
    cW
    vp
    ltrne.a
    ltrne.h
    ltrne.t
    ltrneq2
    bitrd
end
