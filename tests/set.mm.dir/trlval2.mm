include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "clat.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "hllat.mm"
include "anim1i.mm"
include "w3a.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "cbs.mm"
include "crio.mm"
include "eqid.mm"
include "trlval.mm"
include "3adant3.mm"
include "simp1l.mm"
include "simp3l.mm"
include "atbase.mm"
include "syl.mm"
include "ltrncl.mm"
include "syld3an3.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "simp1r.mm"
include "lhpbase.mm"
include "latmcl.mm"
include "simpl3l.mm"
include "simpl3r.mm"
include "breq1.mm"
include "notbid.mm"
include "id.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "oveq1d.mm"
include "eqeq2d.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "com23.mm"
include "sylc.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13l.mm"
include "simp13r.mm"
include "simp3.mm"
include "simp2.mm"
include "ltrnu.mm"
include "syl222anc.mm"
include "eqeq2.mm"
include "biimpd.mm"
include "3exp.mm"
include "com24.mm"
include "ralrimdv.mm"
include "adantr.mm"
include "impbid.mm"
include "riota5.mm"
include "eqtrd.mm"
include "syl3an1.mm"

theorem trlval2
  let cA: class A
  let cP: class P
  let cR: class R
  let cT: class T
  let cF: class F
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let vq: setvar q
  let vx: setvar x
  assume trlval2.l: |- .<_ = ( le ` K )
  assume trlval2.j: |- .\/ = ( join ` K )
  assume trlval2.m: |- ./\ = ( meet ` K )
  assume trlval2.a: |- A = ( Atoms ` K )
  assume trlval2.h: |- H = ( LHyp ` K )
  assume trlval2.t: |- T = ( ( LTrn ` K ) ` W )
  assume trlval2.r: |- R = ( ( trL ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ ( P e. A /\ -. P .<_ W ) ) -> ( R ` F ) = ( ( P .\/ ( F ` P ) ) ./\ W ) )

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
    cK
    clat
    wcel
    #
    @1
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
    cF
    cR
    cfv
    #
    cP
    cP
    cF
    cfv
    #
    c.or
    co
    #
    cW
    c.an
    co
    #
    wceq
    @0
    @2
    @1
    cK
    hllat
    anim1i
    @3
    @4
    @8
    w3a
    #
    @9
    vq
    cv
    #
    cW
    c.le
    wbr
    #
    wn
    #
    vx
    cv
    #
    @14
    @14
    cF
    cfv
    #
    c.or
    co
    #
    cW
    c.an
    co
    #
    wceq
    #
    wi
    #
    vq
    cA
    wral
    #
    vx
    cK
    cbs
    cfv
    #
    crio
    #
    @12
    @3
    @4
    @9
    @25
    wceq
    @8
    vx
    cA
    @24
    cR
    cT
    cF
    cH
    c.or
    cK
    c.le
    c.an
    clat
    cW
    vq
    @24
    eqid
    #
    trlval2.l
    trlval2.j
    trlval2.m
    trlval2.a
    trlval2.h
    trlval2.t
    trlval2.r
    trlval
    3adant3
    @13
    @23
    vx
    @24
    @12
    @13
    @2
    @11
    @24
    wcel
    #
    cW
    @24
    wcel
    #
    @12
    @24
    wcel
    @2
    @1
    @4
    @8
    simp1l
    #
    @13
    @2
    cP
    @24
    wcel
    #
    @10
    @24
    wcel
    #
    @27
    @29
    @13
    @5
    @30
    @3
    @4
    @5
    @7
    simp3l
    cA
    @24
    cP
    cK
    @26
    trlval2.a
    atbase
    syl
    #
    @3
    @4
    @8
    @30
    @31
    @32
    @24
    cT
    cF
    cH
    cK
    clat
    cW
    cP
    @26
    trlval2.h
    trlval2.t
    ltrncl
    syld3an3
    @24
    c.or
    cK
    cP
    @10
    @26
    trlval2.j
    latjcl
    syl3anc
    @13
    @1
    @28
    @2
    @1
    @4
    @8
    simp1r
    @24
    cH
    cK
    cW
    @26
    trlval2.h
    lhpbase
    syl
    @24
    cK
    c.an
    @11
    cW
    @26
    trlval2.m
    latmcl
    syl3anc
    @13
    @17
    @24
    wcel
    #
    wa
    #
    @23
    @17
    @12
    wceq
    #
    @34
    @5
    @7
    @23
    @35
    wi
    @5
    @7
    @3
    @4
    @33
    simpl3l
    @5
    @7
    @3
    @4
    @33
    simpl3r
    @5
    @23
    @7
    @35
    @22
    @7
    @35
    wi
    vq
    cP
    cA
    @14
    cP
    wceq
    #
    @16
    @7
    @21
    @35
    @36
    @15
    @6
    @14
    cP
    cW
    c.le
    breq1
    notbid
    @36
    @20
    @12
    @17
    @36
    @19
    @11
    cW
    c.an
    @36
    @14
    cP
    @18
    @10
    c.or
    @36
    id
    @14
    cP
    cF
    fveq2
    oveq12d
    oveq1d
    eqeq2d
    imbi12d
    rspcv
    com23
    sylc
    @13
    @35
    @23
    wi
    @33
    @13
    @35
    @22
    vq
    cA
    @13
    @16
    @14
    cA
    wcel
    #
    @35
    @21
    @13
    @16
    @37
    @35
    @21
    wi
    #
    @13
    @16
    @37
    w3a
    #
    @12
    @20
    wceq
    #
    @38
    @39
    @3
    @4
    @5
    @7
    @37
    @16
    @40
    @3
    @4
    @8
    @16
    @37
    simp11
    @3
    @4
    @8
    @16
    @37
    simp12
    @5
    @7
    @3
    @4
    @16
    @37
    simp13l
    @5
    @7
    @3
    @4
    @16
    @37
    simp13r
    @13
    @16
    @37
    simp3
    @13
    @16
    @37
    simp2
    cA
    cP
    @14
    cT
    cF
    cH
    c.or
    cK
    c.le
    c.an
    clat
    cW
    trlval2.l
    trlval2.j
    trlval2.m
    trlval2.a
    trlval2.h
    trlval2.t
    ltrnu
    syl222anc
    @40
    @35
    @21
    @12
    @20
    @17
    eqeq2
    biimpd
    syl
    3exp
    com24
    ralrimdv
    adantr
    impbid
    riota5
    eqtrd
    syl3an1
end
