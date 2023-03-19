include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cfv.mm"
include "ccnv.mm"
include "ccom.mm"
include "co.mm"
include "cmee.mm"
include "wceq.mm"
include "simp1.mm"
include "simp2r.mm"
include "simp2l.mm"
include "ltrncnv.mm"
include "syl2anc.mm"
include "ltrnco.mm"
include "syl3anc.mm"
include "ltrnel.mm"
include "3adant2r.mm"
include "eqid.mm"
include "trlval2.mm"
include "oveq2d.mm"
include "cbs.mm"
include "simp1l.mm"
include "simp3l.mm"
include "ltrnat.mm"
include "hlatjcl.mm"
include "simp1r.mm"
include "lhpbase.mm"
include "syl.mm"
include "hlatlej1.mm"
include "atmod3i1.mm"
include "syl131anc.mm"
include "cp1.mm"
include "ltrncoval.mm"
include "syl121anc.mm"
include "coass.mm"
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
include "eqtrd.mm"
include "syl5eq.mm"
include "fveq1d.mm"
include "eqtr3d.mm"
include "lhpjat2.mm"
include "oveq12d.mm"
include "col.mm"
include "hlol.mm"
include "olm11.mm"
include "3eqtrd.mm"

theorem trlcoabs2N
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
  assume trlcoabs.l: |- .<_ = ( le ` K )
  assume trlcoabs.j: |- .\/ = ( join ` K )
  assume trlcoabs.a: |- A = ( Atoms ` K )
  assume trlcoabs.h: |- H = ( LHyp ` K )
  assume trlcoabs.t: |- T = ( ( LTrn ` K ) ` W )
  assume trlcoabs.r: |- R = ( ( trL ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ G e. T ) /\ ( P e. A /\ -. P .<_ W ) ) -> ( ( F ` P ) .\/ ( R ` ( G o. `' F ) ) ) = ( ( F ` P ) .\/ ( G ` P ) ) )

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
    cG
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
    cG
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
    @10
    @10
    @10
    @12
    cfv
    #
    c.or
    co
    #
    cW
    cK
    cmee
    cfv
    #
    co
    #
    c.or
    co
    #
    @15
    @10
    cW
    c.or
    co
    #
    @16
    co
    #
    @10
    cP
    cG
    cfv
    #
    c.or
    co
    #
    @9
    @13
    @17
    @10
    c.or
    @9
    @2
    @12
    cT
    wcel
    #
    @10
    cA
    wcel
    #
    @10
    cW
    c.le
    wbr
    wn
    wa
    #
    @13
    @17
    wceq
    @2
    @5
    @8
    simp1
    #
    @9
    @2
    @4
    @11
    cT
    wcel
    #
    @23
    @26
    @2
    @3
    @4
    @8
    simp2r
    #
    @9
    @2
    @3
    @27
    @26
    @2
    @3
    @4
    @8
    simp2l
    #
    cT
    cF
    cH
    cK
    cW
    trlcoabs.h
    trlcoabs.t
    ltrncnv
    syl2anc
    cT
    cG
    @11
    cH
    cK
    cW
    trlcoabs.h
    trlcoabs.t
    ltrnco
    syl3anc
    #
    @2
    @3
    @8
    @25
    @4
    cA
    cP
    cT
    cF
    cH
    cK
    c.le
    cW
    trlcoabs.l
    trlcoabs.a
    trlcoabs.h
    trlcoabs.t
    ltrnel
    3adant2r
    #
    cA
    @10
    cR
    cT
    @12
    cH
    c.or
    cK
    c.le
    @16
    cW
    trlcoabs.l
    trlcoabs.j
    @16
    eqid
    #
    trlcoabs.a
    trlcoabs.h
    trlcoabs.t
    trlcoabs.r
    trlval2
    syl3anc
    oveq2d
    @9
    @0
    @24
    @15
    cK
    cbs
    cfv
    #
    wcel
    #
    cW
    @33
    wcel
    #
    @10
    @15
    c.le
    wbr
    #
    @18
    @20
    wceq
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
    @24
    @26
    @29
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
    trlcoabs.l
    trlcoabs.a
    trlcoabs.h
    trlcoabs.t
    ltrnat
    syl3anc
    #
    @9
    @0
    @24
    @14
    cA
    wcel
    #
    @34
    @37
    @39
    @9
    @2
    @23
    @24
    @40
    @26
    @30
    @39
    cA
    @10
    cT
    @12
    cH
    cK
    c.le
    cW
    trlcoabs.l
    trlcoabs.a
    trlcoabs.h
    trlcoabs.t
    ltrnat
    syl3anc
    #
    cA
    @33
    c.or
    cK
    @10
    @14
    @33
    eqid
    #
    trlcoabs.j
    trlcoabs.a
    hlatjcl
    syl3anc
    @9
    @1
    @35
    @0
    @1
    @5
    @8
    simp1r
    @33
    cH
    cK
    cW
    @42
    trlcoabs.h
    lhpbase
    syl
    @9
    @0
    @24
    @40
    @36
    @37
    @39
    @41
    cA
    @10
    @14
    c.or
    cK
    c.le
    trlcoabs.l
    trlcoabs.j
    trlcoabs.a
    hlatlej1
    syl3anc
    cA
    @33
    @10
    c.or
    cK
    c.le
    @16
    @15
    cW
    @42
    trlcoabs.l
    trlcoabs.j
    @32
    trlcoabs.a
    atmod3i1
    syl131anc
    @9
    @20
    @22
    cK
    cp1
    cfv
    #
    @16
    co
    #
    @22
    @9
    @15
    @22
    @19
    @43
    @16
    @9
    @14
    @21
    @10
    c.or
    @9
    cP
    @12
    cF
    ccom
    #
    cfv
    #
    @14
    @21
    @9
    @2
    @23
    @3
    @6
    @46
    @14
    wceq
    @26
    @30
    @29
    @38
    cA
    cP
    cT
    @12
    cF
    cH
    cK
    c.le
    cW
    trlcoabs.l
    trlcoabs.a
    trlcoabs.h
    trlcoabs.t
    ltrncoval
    syl121anc
    @9
    cP
    @45
    cG
    @9
    @45
    cG
    @11
    cF
    ccom
    #
    ccom
    #
    cG
    cG
    @11
    cF
    coass
    @9
    @48
    cG
    cid
    @33
    cres
    #
    ccom
    #
    cG
    @9
    @47
    @49
    cG
    @9
    @33
    @33
    cF
    wf1o
    #
    @47
    @49
    wceq
    @9
    @2
    @3
    @51
    @26
    @29
    @33
    cT
    cF
    cH
    cK
    chlt
    cW
    @42
    trlcoabs.h
    trlcoabs.t
    ltrn1o
    syl2anc
    @33
    @33
    cF
    f1ococnv1
    syl
    coeq2d
    @9
    @33
    @33
    cG
    wf1o
    #
    @33
    @33
    cG
    wf
    @50
    cG
    wceq
    @9
    @2
    @4
    @52
    @26
    @28
    @33
    cT
    cG
    cH
    cK
    chlt
    cW
    @42
    trlcoabs.h
    trlcoabs.t
    ltrn1o
    syl2anc
    @33
    @33
    cG
    f1of
    @33
    @33
    cG
    fcoi1
    3syl
    eqtrd
    syl5eq
    fveq1d
    eqtr3d
    oveq2d
    @9
    @2
    @25
    @19
    @43
    wceq
    @26
    @31
    cA
    @10
    @43
    cH
    c.or
    cK
    c.le
    cW
    trlcoabs.l
    trlcoabs.j
    @43
    eqid
    #
    trlcoabs.a
    trlcoabs.h
    lhpjat2
    syl2anc
    oveq12d
    @9
    cK
    col
    wcel
    #
    @22
    @33
    wcel
    #
    @44
    @22
    wceq
    @9
    @0
    @54
    @37
    cK
    hlol
    syl
    @9
    @0
    @24
    @21
    cA
    wcel
    #
    @55
    @37
    @39
    @9
    @2
    @4
    @6
    @56
    @26
    @28
    @38
    cA
    cP
    cT
    cG
    cH
    cK
    c.le
    cW
    trlcoabs.l
    trlcoabs.a
    trlcoabs.h
    trlcoabs.t
    ltrnat
    syl3anc
    cA
    @33
    c.or
    cK
    @10
    @21
    @42
    trlcoabs.j
    trlcoabs.a
    hlatjcl
    syl3anc
    @33
    @43
    cK
    @16
    @22
    @42
    @32
    @53
    olm11
    syl2anc
    eqtrd
    3eqtrd
end
