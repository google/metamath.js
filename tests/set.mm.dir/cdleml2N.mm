include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "w3a.mm"
include "cid.mm"
include "cres.mm"
include "wne.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "simp1.mm"
include "simp21.mm"
include "simp23.mm"
include "tendocl.mm"
include "syl3anc.mm"
include "simp22.mm"
include "cdleml1N.mm"
include "cdlemk.mm"
include "syl121anc.mm"

theorem cdleml2N
  let cB: class B
  let cR: class R
  let cT: class T
  let cU: class U
  let vf: setvar f
  let cE: class E
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let vs: setvar s
  assume cdleml1.b: |- B = ( Base ` K )
  assume cdleml1.h: |- H = ( LHyp ` K )
  assume cdleml1.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdleml1.r: |- R = ( ( trL ` K ) ` W )
  assume cdleml1.e: |- E = ( ( TEndo ` K ) ` W )

  disjoint E s
  disjoint K s
  disjoint R s
  disjoint T s
  disjoint U s
  disjoint V s
  disjoint W s
  disjoint f s
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( U e. E /\ V e. E /\ f e. T ) /\ ( f =/= ( _I |` B ) /\ ( U ` f ) =/= ( _I |` B ) /\ ( V ` f ) =/= ( _I |` B ) ) ) -> E. s e. E ( s ` ( U ` f ) ) = ( V ` f ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cU
    cE
    wcel
    #
    cV
    cE
    wcel
    #
    vf
    cv
    #
    cT
    wcel
    #
    w3a
    #
    @3
    cid
    cB
    cres
    #
    wne
    @3
    cU
    cfv
    #
    @6
    wne
    @3
    cV
    cfv
    #
    @6
    wne
    w3a
    #
    w3a
    #
    @0
    @7
    cT
    wcel
    #
    @8
    cT
    wcel
    #
    @7
    cR
    cfv
    @8
    cR
    cfv
    wceq
    @7
    vs
    cv
    cfv
    @8
    wceq
    vs
    cE
    wrex
    @0
    @5
    @9
    simp1
    #
    @10
    @0
    @1
    @4
    @11
    @13
    @0
    @1
    @2
    @4
    @9
    simp21
    @0
    @1
    @2
    @4
    @9
    simp23
    #
    cU
    cT
    cE
    @3
    cH
    cK
    chlt
    cW
    cdleml1.h
    cdleml1.t
    cdleml1.e
    tendocl
    syl3anc
    @10
    @0
    @2
    @4
    @12
    @13
    @0
    @1
    @2
    @4
    @9
    simp22
    @14
    cV
    cT
    cE
    @3
    cH
    cK
    chlt
    cW
    cdleml1.h
    cdleml1.t
    cdleml1.e
    tendocl
    syl3anc
    cB
    cR
    cT
    cU
    vf
    cE
    cH
    cK
    cV
    cW
    cdleml1.b
    cdleml1.h
    cdleml1.t
    cdleml1.r
    cdleml1.e
    cdleml1N
    vs
    cR
    cT
    cE
    @7
    cH
    cK
    @8
    cW
    cdleml1.h
    cdleml1.t
    cdleml1.r
    cdleml1.e
    cdlemk
    syl121anc
end
