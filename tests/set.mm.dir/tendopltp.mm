include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "cbs.mm"
include "cfv.mm"
include "co.mm"
include "cjn.mm"
include "eqid.mm"
include "clat.mm"
include "simp1l.mm"
include "hllat.mm"
include "syl.mm"
include "simp1.mm"
include "tendoplcl2.mm"
include "trlcl.mm"
include "syl2anc.mm"
include "tendocl.mm"
include "3adant2r.mm"
include "3adant2l.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "simp3.mm"
include "ccom.mm"
include "wceq.mm"
include "simp2l.mm"
include "simp2r.mm"
include "tendopl2.mm"
include "fveq2d.mm"
include "wbr.mm"
include "trlco.mm"
include "eqbrtrd.mm"
include "tendotp.mm"
include "wb.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "lattrd.mm"

theorem tendopltp
  let vt: setvar t
  let cP: class P
  let cR: class R
  let cT: class T
  let cU: class U
  let vf: setvar f
  let cE: class E
  let cF: class F
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cW: class W
  let vs: setvar s
  let cG: class G
  assume tendopl.h: |- H = ( LHyp ` K )
  assume tendopl.t: |- T = ( ( LTrn ` K ) ` W )
  assume tendopl.e: |- E = ( ( TEndo ` K ) ` W )
  assume tendopl.p: |- P = ( s e. E , t e. E |-> ( f e. T |-> ( ( s ` f ) o. ( t ` f ) ) ) )
  assume tendopltp.l: |- .<_ = ( le ` K )
  assume tendopltp.r: |- R = ( ( trL ` K ) ` W )

  disjoint s t
  disjoint E s
  disjoint E t
  disjoint f s
  disjoint f t
  disjoint T f
  disjoint T s
  disjoint T t
  disjoint W f
  disjoint W s
  disjoint W t
  disjoint G f
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( U e. E /\ V e. E ) /\ F e. T ) -> ( R ` ( ( U P V ) ` F ) ) .<_ ( R ` F ) )

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
    cU
    cE
    wcel
    #
    cV
    cE
    wcel
    #
    wa
    #
    cF
    cT
    wcel
    #
    w3a
    #
    cK
    cbs
    cfv
    #
    cK
    c.le
    cF
    cU
    cV
    cP
    co
    cfv
    #
    cR
    cfv
    #
    cF
    cU
    cfv
    #
    cR
    cfv
    #
    cF
    cV
    cfv
    #
    cR
    cfv
    #
    cK
    cjn
    cfv
    #
    co
    #
    cF
    cR
    cfv
    #
    @8
    eqid
    #
    tendopltp.l
    @7
    @0
    cK
    clat
    wcel
    #
    @0
    @1
    @5
    @6
    simp1l
    cK
    hllat
    syl
    #
    @7
    @2
    @9
    cT
    wcel
    @10
    @8
    wcel
    @2
    @5
    @6
    simp1
    #
    vt
    cP
    cT
    cU
    vf
    cE
    cF
    cH
    cK
    cV
    cW
    vs
    tendopl.h
    tendopl.t
    tendopl.e
    tendopl.p
    tendoplcl2
    @8
    cR
    cT
    @9
    cH
    cK
    cW
    @18
    tendopl.h
    tendopl.t
    tendopltp.r
    trlcl
    syl2anc
    @7
    @19
    @12
    @8
    wcel
    #
    @14
    @8
    wcel
    #
    @16
    @8
    wcel
    @20
    @7
    @2
    @11
    cT
    wcel
    #
    @22
    @21
    @2
    @3
    @6
    @24
    @4
    cU
    cT
    cE
    cF
    cH
    cK
    chlt
    cW
    tendopl.h
    tendopl.t
    tendopl.e
    tendocl
    3adant2r
    #
    @8
    cR
    cT
    @11
    cH
    cK
    cW
    @18
    tendopl.h
    tendopl.t
    tendopltp.r
    trlcl
    syl2anc
    #
    @7
    @2
    @13
    cT
    wcel
    #
    @23
    @21
    @2
    @4
    @6
    @27
    @3
    cV
    cT
    cE
    cF
    cH
    cK
    chlt
    cW
    tendopl.h
    tendopl.t
    tendopl.e
    tendocl
    3adant2l
    #
    @8
    cR
    cT
    @13
    cH
    cK
    cW
    @18
    tendopl.h
    tendopl.t
    tendopltp.r
    trlcl
    syl2anc
    #
    @8
    @15
    cK
    @12
    @14
    @18
    @15
    eqid
    #
    latjcl
    syl3anc
    @7
    @2
    @6
    @17
    @8
    wcel
    #
    @21
    @2
    @5
    @6
    simp3
    #
    @8
    cR
    cT
    cF
    cH
    cK
    cW
    @18
    tendopl.h
    tendopl.t
    tendopltp.r
    trlcl
    syl2anc
    #
    @7
    @10
    @11
    @13
    ccom
    #
    cR
    cfv
    #
    @16
    c.le
    @7
    @9
    @34
    cR
    @7
    @3
    @4
    @6
    @9
    @34
    wceq
    @2
    @3
    @4
    @6
    simp2l
    @2
    @3
    @4
    @6
    simp2r
    @32
    vt
    cP
    cT
    cU
    vf
    cE
    cF
    cK
    cV
    cW
    vs
    tendopl.p
    tendopl.t
    tendopl2
    syl3anc
    fveq2d
    @7
    @2
    @24
    @27
    @35
    @16
    c.le
    wbr
    @21
    @25
    @28
    cR
    cT
    @11
    @13
    cH
    @15
    cK
    c.le
    cW
    tendopltp.l
    @30
    tendopl.h
    tendopl.t
    tendopltp.r
    trlco
    syl3anc
    eqbrtrd
    @7
    @12
    @17
    c.le
    wbr
    #
    @14
    @17
    c.le
    wbr
    #
    @16
    @17
    c.le
    wbr
    #
    @2
    @3
    @6
    @36
    @4
    cR
    cU
    cT
    cE
    cF
    cH
    cK
    c.le
    chlt
    cW
    tendopltp.l
    tendopl.h
    tendopl.t
    tendopltp.r
    tendopl.e
    tendotp
    3adant2r
    @2
    @4
    @6
    @37
    @3
    cR
    cV
    cT
    cE
    cF
    cH
    cK
    c.le
    chlt
    cW
    tendopltp.l
    tendopl.h
    tendopl.t
    tendopltp.r
    tendopl.e
    tendotp
    3adant2l
    @7
    @19
    @22
    @23
    @31
    @36
    @37
    wa
    @38
    wb
    @20
    @26
    @29
    @33
    @8
    @15
    cK
    c.le
    @12
    @14
    @17
    @18
    tendopltp.l
    @30
    latjle12
    syl13anc
    mpbi2and
    lattrd
end
