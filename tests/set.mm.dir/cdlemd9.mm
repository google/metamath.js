include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "wceq.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpl3.mm"
include "simpr.mm"
include "cdlemd8.mm"
include "syl112anc.mm"
include "wne.mm"
include "cv.mm"
include "co.mm"
include "wrex.mm"
include "simpl11.mm"
include "simp12l.mm"
include "adantr.mm"
include "ltrnel.mm"
include "syl3anc.mm"
include "necomd.mm"
include "cdlemb2.mm"
include "syl121anc.mm"
include "simp1l1.mm"
include "simp1l2.mm"
include "simp2.mm"
include "simp3l.mm"
include "jca.mm"
include "simp1l3.mm"
include "simp3r.mm"
include "cdlemd7.mm"
include "syl122anc.mm"
include "rexlimdv3a.mm"
include "mpd.mm"
include "pm2.61dane.mm"

theorem cdlemd9
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


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ G e. T ) /\ R e. A ) /\ ( P e. A /\ -. P .<_ W ) /\ ( F ` P ) = ( G ` P ) ) -> ( F ` R ) = ( G ` R ) )

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
    wceq
    #
    w3a
    #
    cR
    cF
    cfv
    cR
    cG
    cfv
    wceq
    #
    @7
    cP
    @9
    @7
    cP
    wceq
    #
    wa
    @5
    @6
    @8
    @11
    @10
    @5
    @6
    @8
    @11
    simpl1
    @5
    @6
    @8
    @11
    simpl2
    @5
    @6
    @8
    @11
    simpl3
    @9
    @11
    simpr
    cA
    cP
    cR
    cT
    cF
    cG
    cH
    c.or
    cK
    c.le
    cW
    cdlemd4.l
    cdlemd4.j
    cdlemd4.a
    cdlemd4.h
    cdlemd4.t
    cdlemd8
    syl112anc
    @9
    @7
    cP
    wne
    #
    wa
    #
    vs
    cv
    #
    cW
    c.le
    wbr
    wn
    #
    @14
    cP
    @7
    c.or
    co
    c.le
    wbr
    wn
    #
    wa
    #
    vs
    cA
    wrex
    #
    @10
    @13
    @0
    @6
    @7
    cA
    wcel
    @7
    cW
    c.le
    wbr
    wn
    wa
    #
    cP
    @7
    wne
    @18
    @0
    @3
    @4
    @6
    @8
    @12
    simpl11
    #
    @5
    @6
    @8
    @12
    simpl2
    #
    @13
    @0
    @1
    @6
    @19
    @20
    @9
    @1
    @12
    @1
    @2
    @0
    @4
    @6
    @8
    simp12l
    adantr
    @21
    cA
    cP
    cT
    cF
    cH
    cK
    c.le
    cW
    cdlemd4.l
    cdlemd4.a
    cdlemd4.h
    cdlemd4.t
    ltrnel
    syl3anc
    @13
    @7
    cP
    @9
    @12
    simpr
    necomd
    cA
    cP
    @7
    cH
    c.or
    cK
    c.le
    cW
    vs
    cdlemd4.l
    cdlemd4.j
    cdlemd4.a
    cdlemd4.h
    cdlemb2
    syl121anc
    @13
    @17
    @10
    vs
    cA
    @13
    @14
    cA
    wcel
    #
    @17
    w3a
    #
    @5
    @6
    @22
    @15
    wa
    @8
    @16
    @10
    @5
    @6
    @8
    @12
    @22
    @17
    simp1l1
    @5
    @6
    @8
    @12
    @22
    @17
    simp1l2
    @23
    @22
    @15
    @13
    @22
    @17
    simp2
    @13
    @22
    @15
    @16
    simp3l
    jca
    @5
    @6
    @8
    @12
    @22
    @17
    simp1l3
    @13
    @22
    @15
    @16
    simp3r
    cA
    cP
    @14
    cR
    cT
    cF
    cG
    cH
    c.or
    cK
    c.le
    cW
    cdlemd4.l
    cdlemd4.j
    cdlemd4.a
    cdlemd4.h
    cdlemd4.t
    cdlemd7
    syl122anc
    rexlimdv3a
    mpd
    pm2.61dane
end
