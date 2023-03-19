include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cfv.mm"
include "simp3l.mm"
include "cbs.mm"
include "wb.mm"
include "eqid.mm"
include "atbase.mm"
include "adantr.mm"
include "ltrnatb.mm"
include "syl3an3.mm"
include "mpbid.mm"
include "simp3r.mm"
include "simp1.mm"
include "simp2.mm"
include "syl.mm"
include "simp1r.mm"
include "lhpbase.mm"
include "ltrnle.mm"
include "syl112anc.mm"
include "wceq.mm"
include "clat.mm"
include "simp1l.mm"
include "hllat.mm"
include "latref.mm"
include "syl2anc.mm"
include "ltrnval1.mm"
include "breq2d.mm"
include "bitrd.mm"
include "mtbid.mm"
include "jca.mm"

theorem ltrnel
  let cA: class A
  let cP: class P
  let cT: class T
  let cF: class F
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cW: class W
  assume ltrnel.l: |- .<_ = ( le ` K )
  assume ltrnel.a: |- A = ( Atoms ` K )
  assume ltrnel.h: |- H = ( LHyp ` K )
  assume ltrnel.t: |- T = ( ( LTrn ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ ( P e. A /\ -. P .<_ W ) ) -> ( ( F ` P ) e. A /\ -. ( F ` P ) .<_ W ) )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    cF
    cT
    wcel
    #
    cP
    cA
    wcel
    #
    cP
    cW
    c.le
    wbr
    #
    wn
    #
    wa
    #
    w3a
    #
    cP
    cF
    cfv
    #
    cA
    wcel
    #
    @9
    cW
    c.le
    wbr
    #
    wn
    @8
    @4
    @10
    @2
    @3
    @4
    @6
    simp3l
    #
    @7
    @2
    @3
    cP
    cK
    cbs
    cfv
    #
    wcel
    #
    @4
    @10
    wb
    @4
    @14
    @6
    cA
    @13
    cP
    cK
    @13
    eqid
    #
    ltrnel.a
    atbase
    #
    adantr
    cA
    @13
    cP
    cT
    cF
    cH
    cK
    cW
    @15
    ltrnel.a
    ltrnel.h
    ltrnel.t
    ltrnatb
    syl3an3
    mpbid
    @8
    @5
    @11
    @2
    @3
    @4
    @6
    simp3r
    @8
    @5
    @9
    cW
    cF
    cfv
    #
    c.le
    wbr
    #
    @11
    @8
    @2
    @3
    @14
    cW
    @13
    wcel
    #
    @5
    @18
    wb
    @2
    @3
    @7
    simp1
    #
    @2
    @3
    @7
    simp2
    #
    @8
    @4
    @14
    @12
    @16
    syl
    @8
    @1
    @19
    @0
    @1
    @3
    @7
    simp1r
    @13
    cH
    cK
    cW
    @15
    ltrnel.h
    lhpbase
    syl
    #
    @13
    cT
    cF
    cH
    cK
    c.le
    chlt
    cW
    cP
    cW
    @15
    ltrnel.l
    ltrnel.h
    ltrnel.t
    ltrnle
    syl112anc
    @8
    @17
    cW
    @9
    c.le
    @8
    @2
    @3
    @19
    cW
    cW
    c.le
    wbr
    #
    @17
    cW
    wceq
    @20
    @21
    @22
    @8
    cK
    clat
    wcel
    #
    @19
    @23
    @8
    @0
    @24
    @0
    @1
    @3
    @7
    simp1l
    cK
    hllat
    syl
    @22
    @13
    cK
    c.le
    cW
    @15
    ltrnel.l
    latref
    syl2anc
    @13
    cT
    cF
    cH
    cK
    c.le
    chlt
    cW
    cW
    @15
    ltrnel.l
    ltrnel.h
    ltrnel.t
    ltrnval1
    syl112anc
    breq2d
    bitrd
    mtbid
    jca
end
