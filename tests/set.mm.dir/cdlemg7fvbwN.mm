include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cv.mm"
include "cmee.mm"
include "cfv.mm"
include "co.mm"
include "cjn.mm"
include "wceq.mm"
include "wrex.mm"
include "eqid.mm"
include "lhpmcvr2.mm"
include "3adant3.mm"
include "simp11.mm"
include "simp2.mm"
include "simp3l.mm"
include "jca.mm"
include "simp12.mm"
include "simp13.mm"
include "simp3r.mm"
include "cdlemg2fv.mm"
include "syl122anc.mm"
include "clat.mm"
include "simp11l.mm"
include "hllat.mm"
include "syl.mm"
include "ltrnel.mm"
include "simpld.mm"
include "syl3anc.mm"
include "atbase.mm"
include "simp12l.mm"
include "simp11r.mm"
include "lhpbase.mm"
include "latmcl.mm"
include "latjcl.mm"
include "eqeltrd.mm"
include "simprd.mm"
include "latlej1.mm"
include "wi.mm"
include "lattr.mm"
include "syl13anc.mm"
include "mpand.mm"
include "mtod.mm"
include "breq1d.mm"
include "mtbird.mm"
include "rexlimdv3a.mm"
include "mpd.mm"

theorem cdlemg7fvbwN
  let cA: class A
  let cB: class B
  let cT: class T
  let cF: class F
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let cX: class X
  let vr: setvar r
  let cG: class G
  let c.or: class .\/
  let cP: class P
  let cQ: class Q
  let cV: class V
  assume cdlemg4.l: |- .<_ = ( le ` K )
  assume cdlemg4.a: |- A = ( Atoms ` K )
  assume cdlemg4.h: |- H = ( LHyp ` K )
  assume cdlemg4.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemg4.b: |- B = ( Base ` K )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( X e. B /\ -. X .<_ W ) /\ F e. T ) -> ( ( F ` X ) e. B /\ -. ( F ` X ) .<_ W ) )

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
    cX
    cB
    wcel
    #
    cX
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    cF
    cT
    wcel
    #
    w3a
    #
    vr
    cv
    #
    cW
    c.le
    wbr
    wn
    #
    @8
    cX
    cW
    cK
    cmee
    cfv
    #
    co
    #
    cK
    cjn
    cfv
    #
    co
    cX
    wceq
    #
    wa
    #
    vr
    cA
    wrex
    #
    cX
    cF
    cfv
    #
    cB
    wcel
    #
    @16
    cW
    c.le
    wbr
    #
    wn
    #
    wa
    #
    @2
    @5
    @15
    @6
    cA
    cB
    cH
    @12
    cK
    c.le
    @10
    cW
    cX
    vr
    cdlemg4.b
    cdlemg4.l
    @12
    eqid
    #
    @10
    eqid
    #
    cdlemg4.a
    cdlemg4.h
    lhpmcvr2
    3adant3
    @7
    @14
    @20
    vr
    cA
    @7
    @8
    cA
    wcel
    #
    @14
    w3a
    #
    @17
    @19
    @24
    @16
    @8
    cF
    cfv
    #
    @11
    @12
    co
    #
    cB
    @24
    @2
    @23
    @9
    wa
    #
    @5
    @6
    @13
    @16
    @26
    wceq
    @2
    @5
    @6
    @23
    @14
    simp11
    #
    @24
    @23
    @9
    @7
    @23
    @14
    simp2
    @7
    @23
    @9
    @13
    simp3l
    jca
    #
    @2
    @5
    @6
    @23
    @14
    simp12
    @2
    @5
    @6
    @23
    @14
    simp13
    #
    @7
    @23
    @9
    @13
    simp3r
    cA
    cB
    @8
    cT
    cF
    cH
    @12
    cK
    c.le
    @10
    cW
    cX
    cdlemg4.h
    cdlemg4.t
    cdlemg4.l
    @21
    cdlemg4.a
    @22
    cdlemg4.b
    cdlemg2fv
    syl122anc
    #
    @24
    cK
    clat
    wcel
    #
    @25
    cB
    wcel
    #
    @11
    cB
    wcel
    #
    @26
    cB
    wcel
    #
    @24
    @0
    @32
    @0
    @1
    @5
    @6
    @23
    @14
    simp11l
    cK
    hllat
    syl
    #
    @24
    @25
    cA
    wcel
    #
    @33
    @24
    @2
    @6
    @27
    @37
    @28
    @30
    @29
    @2
    @6
    @27
    w3a
    #
    @37
    @25
    cW
    c.le
    wbr
    #
    wn
    #
    cA
    @8
    cT
    cF
    cH
    cK
    c.le
    cW
    cdlemg4.l
    cdlemg4.a
    cdlemg4.h
    cdlemg4.t
    ltrnel
    #
    simpld
    syl3anc
    cA
    cB
    @25
    cK
    cdlemg4.b
    cdlemg4.a
    atbase
    syl
    #
    @24
    @32
    @3
    cW
    cB
    wcel
    #
    @34
    @36
    @3
    @4
    @2
    @6
    @23
    @14
    simp12l
    @24
    @1
    @43
    @0
    @1
    @5
    @6
    @23
    @14
    simp11r
    cB
    cH
    cK
    cW
    cdlemg4.b
    cdlemg4.h
    lhpbase
    syl
    #
    cB
    cK
    @10
    cX
    cW
    cdlemg4.b
    @22
    latmcl
    syl3anc
    #
    cB
    @12
    cK
    @25
    @11
    cdlemg4.b
    @21
    latjcl
    syl3anc
    #
    eqeltrd
    @24
    @18
    @26
    cW
    c.le
    wbr
    #
    @24
    @47
    @39
    @24
    @2
    @6
    @27
    @40
    @28
    @30
    @29
    @38
    @37
    @40
    @41
    simprd
    syl3anc
    @24
    @25
    @26
    c.le
    wbr
    #
    @47
    @39
    @24
    @32
    @33
    @34
    @48
    @36
    @42
    @45
    cB
    @12
    cK
    c.le
    @25
    @11
    cdlemg4.b
    cdlemg4.l
    @21
    latlej1
    syl3anc
    @24
    @32
    @33
    @35
    @43
    @48
    @47
    wa
    @39
    wi
    @36
    @42
    @46
    @44
    cB
    cK
    c.le
    @25
    @26
    cW
    cdlemg4.b
    cdlemg4.l
    lattr
    syl13anc
    mpand
    mtod
    @24
    @16
    @26
    cW
    c.le
    @31
    breq1d
    mtbird
    jca
    rexlimdv3a
    mpd
end
