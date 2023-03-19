include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cid.mm"
include "cres.mm"
include "wne.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "wrex.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "ralinexa.mm"
include "nne.mm"
include "biimpi.mm"
include "imim2i.mm"
include "ralimi.mm"
include "sylbir.mm"
include "ltrnid.mm"
include "syl5ib.mm"
include "necon1ad.mm"
include "3impia.mm"

theorem ltrnnid
  let cA: class A
  let cB: class B
  let cT: class T
  let cF: class F
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let vp: setvar p
  let vx: setvar x
  assume ltrneq.b: |- B = ( Base ` K )
  assume ltrneq.l: |- .<_ = ( le ` K )
  assume ltrneq.a: |- A = ( Atoms ` K )
  assume ltrneq.h: |- H = ( LHyp ` K )
  assume ltrneq.t: |- T = ( ( LTrn ` K ) ` W )

  disjoint A p
  disjoint B p
  disjoint F p
  disjoint H p
  disjoint K p
  disjoint T p
  disjoint W p
  disjoint p x
  disjoint A x
  disjoint B x
  disjoint F x
  disjoint H x
  disjoint K x
  disjoint .<_ x
  disjoint T x
  disjoint W x
  assert |- ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ F =/= ( _I |` B ) ) -> E. p e. A ( -. p .<_ W /\ ( F ` p ) =/= p ) )

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
    cF
    cid
    cB
    cres
    #
    wne
    vp
    cv
    #
    cW
    c.le
    wbr
    wn
    #
    @3
    cF
    cfv
    #
    @3
    wne
    #
    wa
    vp
    cA
    wrex
    #
    @0
    @1
    wa
    #
    @7
    cF
    @2
    @7
    wn
    #
    @4
    @5
    @3
    wceq
    #
    wi
    #
    vp
    cA
    wral
    #
    @8
    cF
    @2
    wceq
    @9
    @4
    @6
    wn
    #
    wi
    #
    vp
    cA
    wral
    @12
    @4
    @6
    vp
    cA
    ralinexa
    @14
    @11
    vp
    cA
    @13
    @10
    @4
    @13
    @10
    @5
    @3
    nne
    biimpi
    imim2i
    ralimi
    sylbir
    cA
    cB
    cT
    cF
    cH
    cK
    c.le
    cW
    vp
    ltrneq.b
    ltrneq.l
    ltrneq.a
    ltrneq.h
    ltrneq.t
    ltrnid
    syl5ib
    necon1ad
    3impia
end
