include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "cbs.mm"
include "wceq.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3l.mm"
include "eqid.mm"
include "atbase.mm"
include "syl.mm"
include "simp1r.mm"
include "lhpbase.mm"
include "ltrnm.mm"
include "syl112anc.mm"
include "simp3r.mm"
include "cal.mm"
include "wb.mm"
include "simp1l.mm"
include "hlatl.mm"
include "atnle.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "fveq2d.mm"
include "eqtr3d.mm"
include "clat.mm"
include "hllat.mm"
include "latref.mm"
include "syl2anc.mm"
include "ltrnval1.mm"
include "oveq2d.mm"
include "cops.mm"
include "hlop.mm"
include "op0cl.mm"
include "op0le.mm"
include "3eqtr3d.mm"

theorem ltrnmwOLD
  let cA: class A
  let cP: class P
  let cT: class T
  let cF: class F
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let c.0: class .0.
  assume ltrnmwOLD.l: |- .<_ = ( le ` K )
  assume ltrnmwOLD.m: |- ./\ = ( meet ` K )
  assume ltrnmwOLD.z: |- .0. = ( 0. ` K )
  assume ltrnmwOLD.a: |- A = ( Atoms ` K )
  assume ltrnmwOLD.h: |- H = ( LHyp ` K )
  assume ltrnmwOLD.t: |- T = ( ( LTrn ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ ( P e. A /\ -. P .<_ W ) ) -> ( ( F ` P ) ./\ W ) = .0. )

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
    cW
    cF
    cfv
    #
    c.an
    co
    #
    c.0
    cF
    cfv
    #
    @8
    cW
    c.an
    co
    c.0
    @7
    cP
    cW
    c.an
    co
    #
    cF
    cfv
    #
    @10
    @11
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
    cW
    @14
    wcel
    #
    @13
    @10
    wceq
    @2
    @3
    @6
    simp1
    #
    @2
    @3
    @6
    simp2
    #
    @7
    @4
    @15
    @2
    @3
    @4
    @5
    simp3l
    #
    cA
    @14
    cP
    cK
    @14
    eqid
    #
    ltrnmwOLD.a
    atbase
    syl
    @7
    @1
    @16
    @0
    @1
    @3
    @6
    simp1r
    @14
    cH
    cK
    cW
    @20
    ltrnmwOLD.h
    lhpbase
    syl
    #
    @14
    cT
    cF
    cH
    cK
    c.an
    cW
    cP
    cW
    @20
    ltrnmwOLD.m
    ltrnmwOLD.h
    ltrnmwOLD.t
    ltrnm
    syl112anc
    @7
    @12
    c.0
    cF
    @7
    @5
    @12
    c.0
    wceq
    #
    @2
    @3
    @4
    @5
    simp3r
    @7
    cK
    cal
    wcel
    #
    @4
    @16
    @5
    @22
    wb
    @7
    @0
    @23
    @0
    @1
    @3
    @6
    simp1l
    #
    cK
    hlatl
    syl
    @19
    @21
    cA
    @14
    cP
    cK
    c.le
    c.an
    cW
    c.0
    @20
    ltrnmwOLD.l
    ltrnmwOLD.m
    ltrnmwOLD.z
    ltrnmwOLD.a
    atnle
    syl3anc
    mpbid
    fveq2d
    eqtr3d
    @7
    @9
    cW
    @8
    c.an
    @7
    @2
    @3
    @16
    cW
    cW
    c.le
    wbr
    #
    @9
    cW
    wceq
    @17
    @18
    @21
    @7
    cK
    clat
    wcel
    #
    @16
    @25
    @7
    @0
    @26
    @24
    cK
    hllat
    syl
    @21
    @14
    cK
    c.le
    cW
    @20
    ltrnmwOLD.l
    latref
    syl2anc
    @14
    cT
    cF
    cH
    cK
    c.le
    chlt
    cW
    cW
    @20
    ltrnmwOLD.l
    ltrnmwOLD.h
    ltrnmwOLD.t
    ltrnval1
    syl112anc
    oveq2d
    @7
    @2
    @3
    c.0
    @14
    wcel
    #
    c.0
    cW
    c.le
    wbr
    #
    @11
    c.0
    wceq
    @17
    @18
    @7
    cK
    cops
    wcel
    #
    @27
    @7
    @0
    @29
    @24
    cK
    hlop
    syl
    #
    @14
    cK
    c.0
    @20
    ltrnmwOLD.z
    op0cl
    syl
    @7
    @29
    @16
    @28
    @30
    @21
    @14
    cK
    c.le
    cW
    c.0
    @20
    ltrnmwOLD.l
    ltrnmwOLD.z
    op0le
    syl2anc
    @14
    cT
    cF
    cH
    cK
    c.le
    chlt
    cW
    c.0
    @20
    ltrnmwOLD.l
    ltrnmwOLD.h
    ltrnmwOLD.t
    ltrnval1
    syl112anc
    3eqtr3d
end
