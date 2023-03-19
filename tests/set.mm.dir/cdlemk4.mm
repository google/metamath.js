include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "ccnv.mm"
include "ccom.mm"
include "simp1l.mm"
include "simp1.mm"
include "simp2l.mm"
include "simp3l.mm"
include "ltrnat.mm"
include "syl3anc.mm"
include "simp2r.mm"
include "hlatlej1.mm"
include "wceq.mm"
include "clat.mm"
include "hllat.mm"
include "syl.mm"
include "atbase.mm"
include "latjcl.mm"
include "simp1r.mm"
include "lhpbase.mm"
include "hlatlej2.mm"
include "atmod3i1.mm"
include "syl131anc.mm"
include "ltrncnv.mm"
include "syl2anc.mm"
include "ltrnco.mm"
include "ltrnel.mm"
include "syld3an2.mm"
include "trlval2.mm"
include "cid.mm"
include "cres.mm"
include "wf1o.mm"
include "ltrn1o.mm"
include "f1ococnv1.mm"
include "coeq2d.mm"
include "wf.mm"
include "f1of.mm"
include "fcoi1.mm"
include "3syl.mm"
include "eqtr2d.mm"
include "coass.mm"
include "syl6eqr.mm"
include "fveq1d.mm"
include "ltrncoval.mm"
include "syl121anc.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "cp1.mm"
include "eqid.mm"
include "lhpjat2.mm"
include "col.mm"
include "hlol.mm"
include "olm11.mm"
include "3eqtr4rd.mm"
include "breqtrd.mm"

theorem cdlemk4
  let cA: class A
  let cB: class B
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
  let cX: class X
  assume cdlemk.b: |- B = ( Base ` K )
  assume cdlemk.l: |- .<_ = ( le ` K )
  assume cdlemk.j: |- .\/ = ( join ` K )
  assume cdlemk.a: |- A = ( Atoms ` K )
  assume cdlemk.h: |- H = ( LHyp ` K )
  assume cdlemk.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemk.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemk.m: |- ./\ = ( meet ` K )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ X e. T ) /\ ( P e. A /\ -. P .<_ W ) ) -> ( F ` P ) .<_ ( ( X ` P ) .\/ ( R ` ( X o. `' F ) ) ) )

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
    cX
    cT
    wcel
    #
    wa
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
    @10
    cP
    cX
    cfv
    #
    c.or
    co
    #
    @11
    cX
    cF
    ccnv
    #
    ccom
    #
    cR
    cfv
    #
    c.or
    co
    #
    c.le
    @9
    @0
    @10
    cA
    wcel
    #
    @11
    cA
    wcel
    #
    @10
    @12
    c.le
    wbr
    @0
    @1
    @5
    @8
    simp1l
    #
    @9
    @2
    @3
    @6
    @17
    @2
    @5
    @8
    simp1
    #
    @2
    @3
    @4
    @8
    simp2l
    #
    @2
    @5
    @6
    @7
    simp3l
    #
    cA
    cP
    cT
    cF
    cH
    cK
    c.le
    cW
    cdlemk.l
    cdlemk.a
    cdlemk.h
    cdlemk.t
    ltrnat
    syl3anc
    #
    @9
    @2
    @4
    @6
    @18
    @20
    @2
    @3
    @4
    @8
    simp2r
    #
    @22
    cA
    cP
    cT
    cX
    cH
    cK
    c.le
    cW
    cdlemk.l
    cdlemk.a
    cdlemk.h
    cdlemk.t
    ltrnat
    syl3anc
    #
    cA
    @10
    @11
    c.or
    cK
    c.le
    cdlemk.l
    cdlemk.j
    cdlemk.a
    hlatlej1
    syl3anc
    @9
    @11
    @12
    cW
    c.an
    co
    #
    c.or
    co
    #
    @12
    @11
    cW
    c.or
    co
    #
    c.an
    co
    #
    @16
    @12
    @9
    @0
    @18
    @12
    cB
    wcel
    #
    cW
    cB
    wcel
    #
    @11
    @12
    c.le
    wbr
    #
    @27
    @29
    wceq
    @19
    @25
    @9
    cK
    clat
    wcel
    #
    @10
    cB
    wcel
    #
    @11
    cB
    wcel
    #
    @30
    @9
    @0
    @33
    @19
    cK
    hllat
    syl
    @9
    @17
    @34
    @23
    cA
    cB
    @10
    cK
    cdlemk.b
    cdlemk.a
    atbase
    syl
    @9
    @18
    @35
    @25
    cA
    cB
    @11
    cK
    cdlemk.b
    cdlemk.a
    atbase
    syl
    cB
    c.or
    cK
    @10
    @11
    cdlemk.b
    cdlemk.j
    latjcl
    syl3anc
    #
    @9
    @1
    @31
    @0
    @1
    @5
    @8
    simp1r
    cB
    cH
    cK
    cW
    cdlemk.b
    cdlemk.h
    lhpbase
    syl
    @9
    @0
    @17
    @18
    @32
    @19
    @23
    @25
    cA
    @10
    @11
    c.or
    cK
    c.le
    cdlemk.l
    cdlemk.j
    cdlemk.a
    hlatlej2
    syl3anc
    cA
    cB
    @11
    c.or
    cK
    c.le
    c.an
    @12
    cW
    cdlemk.b
    cdlemk.l
    cdlemk.j
    cdlemk.m
    cdlemk.a
    atmod3i1
    syl131anc
    @9
    @15
    @26
    @11
    c.or
    @9
    @15
    @10
    @10
    @14
    cfv
    #
    c.or
    co
    #
    cW
    c.an
    co
    #
    @26
    @9
    @2
    @14
    cT
    wcel
    #
    @17
    @10
    cW
    c.le
    wbr
    wn
    wa
    #
    @15
    @39
    wceq
    @20
    @9
    @2
    @4
    @13
    cT
    wcel
    #
    @40
    @20
    @24
    @9
    @2
    @3
    @42
    @20
    @21
    cT
    cF
    cH
    cK
    cW
    cdlemk.h
    cdlemk.t
    ltrncnv
    syl2anc
    cT
    cX
    @13
    cH
    cK
    cW
    cdlemk.h
    cdlemk.t
    ltrnco
    syl3anc
    #
    @2
    @3
    @5
    @8
    @41
    @21
    cA
    cP
    cT
    cF
    cH
    cK
    c.le
    cW
    cdlemk.l
    cdlemk.a
    cdlemk.h
    cdlemk.t
    ltrnel
    syld3an2
    cA
    @10
    cR
    cT
    @14
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemk.l
    cdlemk.j
    cdlemk.m
    cdlemk.a
    cdlemk.h
    cdlemk.t
    cdlemk.r
    trlval2
    syl3anc
    @9
    @38
    @12
    cW
    c.an
    @9
    @12
    @38
    @9
    @11
    @37
    @10
    c.or
    @9
    @11
    cP
    @14
    cF
    ccom
    #
    cfv
    #
    @37
    @9
    cP
    cX
    @44
    @9
    cX
    cX
    @13
    cF
    ccom
    #
    ccom
    #
    @44
    @9
    @47
    cX
    cid
    cB
    cres
    #
    ccom
    #
    cX
    @9
    @46
    @48
    cX
    @9
    cB
    cB
    cF
    wf1o
    #
    @46
    @48
    wceq
    @9
    @2
    @3
    @50
    @20
    @21
    cB
    cT
    cF
    cH
    cK
    chlt
    cW
    cdlemk.b
    cdlemk.h
    cdlemk.t
    ltrn1o
    syl2anc
    cB
    cB
    cF
    f1ococnv1
    syl
    coeq2d
    @9
    cB
    cB
    cX
    wf1o
    #
    cB
    cB
    cX
    wf
    @49
    cX
    wceq
    @9
    @2
    @4
    @51
    @20
    @24
    cB
    cT
    cX
    cH
    cK
    chlt
    cW
    cdlemk.b
    cdlemk.h
    cdlemk.t
    ltrn1o
    syl2anc
    cB
    cB
    cX
    f1of
    cB
    cB
    cX
    fcoi1
    3syl
    eqtr2d
    cX
    @13
    cF
    coass
    syl6eqr
    fveq1d
    @9
    @2
    @40
    @3
    @6
    @45
    @37
    wceq
    @20
    @43
    @21
    @22
    cA
    cP
    cT
    @14
    cF
    cH
    cK
    c.le
    cW
    cdlemk.l
    cdlemk.a
    cdlemk.h
    cdlemk.t
    ltrncoval
    syl121anc
    eqtrd
    oveq2d
    eqcomd
    oveq1d
    eqtrd
    oveq2d
    @9
    @29
    @12
    cK
    cp1
    cfv
    #
    c.an
    co
    #
    @12
    @9
    @28
    @52
    @12
    c.an
    @9
    @2
    @18
    @11
    cW
    c.le
    wbr
    wn
    wa
    #
    @28
    @52
    wceq
    @20
    @2
    @4
    @5
    @8
    @54
    @24
    cA
    cP
    cT
    cX
    cH
    cK
    c.le
    cW
    cdlemk.l
    cdlemk.a
    cdlemk.h
    cdlemk.t
    ltrnel
    syld3an2
    cA
    @11
    @52
    cH
    c.or
    cK
    c.le
    cW
    cdlemk.l
    cdlemk.j
    @52
    eqid
    #
    cdlemk.a
    cdlemk.h
    lhpjat2
    syl2anc
    oveq2d
    @9
    cK
    col
    wcel
    #
    @30
    @53
    @12
    wceq
    @9
    @0
    @56
    @19
    cK
    hlol
    syl
    @36
    cB
    @52
    cK
    c.an
    @12
    cdlemk.b
    cdlemk.m
    @55
    olm11
    syl2anc
    eqtr2d
    3eqtr4rd
    breqtrd
end
