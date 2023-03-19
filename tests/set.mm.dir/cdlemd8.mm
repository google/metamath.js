include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "wceq.mm"
include "cid.mm"
include "cbs.mm"
include "cres.mm"
include "simp3r.mm"
include "wb.mm"
include "simp11.mm"
include "simp12l.mm"
include "simp2.mm"
include "eqid.mm"
include "ltrnideq.mm"
include "syl3anc.mm"
include "mpbird.mm"
include "fveq1d.mm"
include "simp3l.mm"
include "eqtr3d.mm"
include "simp12r.mm"
include "eqtr4d.mm"

theorem cdlemd8
  let cA: class A
  let cP: class P
  let cR: class R
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let vs: setvar s
  let cQ: class Q
  assume cdlemd4.l: |- .<_ = ( le ` K )
  assume cdlemd4.j: |- .\/ = ( join ` K )
  assume cdlemd4.a: |- A = ( Atoms ` K )
  assume cdlemd4.h: |- H = ( LHyp ` K )
  assume cdlemd4.t: |- T = ( ( LTrn ` K ) ` W )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ G e. T ) /\ R e. A ) /\ ( P e. A /\ -. P .<_ W ) /\ ( ( F ` P ) = ( G ` P ) /\ ( F ` P ) = P ) ) -> ( F ` R ) = ( G ` R ) )

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
    wa
    #
    cR
    cA
    wcel
    #
    w3a
    #
    cP
    cA
    wcel
    cP
    cW
    c.le
    wbr
    wn
    wa
    #
    cP
    cF
    cfv
    #
    cP
    cG
    cfv
    #
    wceq
    #
    @7
    cP
    wceq
    #
    wa
    #
    w3a
    #
    cR
    cF
    cfv
    cR
    cid
    cK
    cbs
    cfv
    #
    cres
    #
    cfv
    cR
    cG
    cfv
    @12
    cR
    cF
    @14
    @12
    cF
    @14
    wceq
    #
    @10
    @5
    @6
    @9
    @10
    simp3r
    #
    @12
    @0
    @1
    @6
    @15
    @10
    wb
    @0
    @3
    @4
    @6
    @11
    simp11
    #
    @1
    @2
    @0
    @4
    @6
    @11
    simp12l
    @5
    @6
    @11
    simp2
    #
    cA
    @13
    cP
    cT
    cF
    cH
    cK
    c.le
    cW
    @13
    eqid
    #
    cdlemd4.l
    cdlemd4.a
    cdlemd4.h
    cdlemd4.t
    ltrnideq
    syl3anc
    mpbird
    fveq1d
    @12
    cR
    cG
    @14
    @12
    cG
    @14
    wceq
    #
    @8
    cP
    wceq
    #
    @12
    @7
    @8
    cP
    @5
    @6
    @9
    @10
    simp3l
    @16
    eqtr3d
    @12
    @0
    @2
    @6
    @20
    @21
    wb
    @17
    @1
    @2
    @0
    @4
    @6
    @11
    simp12r
    @18
    cA
    @13
    cP
    cT
    cG
    cH
    cK
    c.le
    cW
    @19
    cdlemd4.l
    cdlemd4.a
    cdlemd4.h
    cdlemd4.t
    ltrnideq
    syl3anc
    mpbird
    fveq1d
    eqtr4d
end
