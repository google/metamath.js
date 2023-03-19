include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "ccnv.mm"
include "ccom.mm"
include "co.mm"
include "wceq.mm"
include "simp1l.mm"
include "simp1r.mm"
include "simp21.mm"
include "simp1.mm"
include "simp23.mm"
include "simp22.mm"
include "ltrncnv.mm"
include "syl2anc.mm"
include "ltrnco.mm"
include "syl3anc.mm"
include "tendovalco.mm"
include "syl32anc.mm"
include "coass.mm"
include "cid.mm"
include "cres.mm"
include "wf1o.mm"
include "ltrn1o.mm"
include "f1ococnv1.mm"
include "syl.mm"
include "coeq2d.mm"
include "wf.mm"
include "f1of.mm"
include "fcoi1.mm"
include "3syl.mm"
include "eqtrd.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "eqtr3d.mm"
include "fveq1d.mm"
include "tendocl.mm"
include "simp3l.mm"
include "ltrncoval.mm"
include "syl121anc.mm"
include "ltrnel.mm"
include "syld3an2.mm"
include "cdlemi1.mm"
include "eqbrtrd.mm"

theorem cdlemi2
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cT: class T
  let cU: class U
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  assume cdlemi.b: |- B = ( Base ` K )
  assume cdlemi.l: |- .<_ = ( le ` K )
  assume cdlemi.j: |- .\/ = ( join ` K )
  assume cdlemi.m: |- ./\ = ( meet ` K )
  assume cdlemi.a: |- A = ( Atoms ` K )
  assume cdlemi.h: |- H = ( LHyp ` K )
  assume cdlemi.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemi.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemi.e: |- E = ( ( TEndo ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( U e. E /\ F e. T /\ G e. T ) /\ ( P e. A /\ -. P .<_ W ) ) -> ( ( U ` G ) ` P ) .<_ ( ( ( U ` F ) ` P ) .\/ ( R ` ( G o. `' F ) ) ) )

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
    cF
    cT
    wcel
    #
    cG
    cT
    wcel
    #
    w3a
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
    cG
    cU
    cfv
    #
    cfv
    #
    cP
    cF
    cU
    cfv
    #
    cfv
    #
    cG
    cF
    ccnv
    #
    ccom
    #
    cU
    cfv
    #
    cfv
    #
    @14
    @16
    cR
    cfv
    c.or
    co
    #
    c.le
    @10
    cP
    @17
    @13
    ccom
    #
    cfv
    #
    @12
    @18
    @10
    cP
    @20
    @11
    @10
    @16
    cF
    ccom
    #
    cU
    cfv
    #
    @20
    @11
    @10
    @0
    @1
    @3
    @16
    cT
    wcel
    #
    @4
    @23
    @20
    wceq
    @0
    @1
    @6
    @9
    simp1l
    @0
    @1
    @6
    @9
    simp1r
    @2
    @3
    @4
    @5
    @9
    simp21
    #
    @10
    @2
    @5
    @15
    cT
    wcel
    #
    @24
    @2
    @6
    @9
    simp1
    #
    @2
    @3
    @4
    @5
    @9
    simp23
    #
    @10
    @2
    @4
    @26
    @27
    @2
    @3
    @4
    @5
    @9
    simp22
    #
    cT
    cF
    cH
    cK
    cW
    cdlemi.h
    cdlemi.t
    ltrncnv
    syl2anc
    cT
    cG
    @15
    cH
    cK
    cW
    cdlemi.h
    cdlemi.t
    ltrnco
    syl3anc
    #
    @29
    cU
    cT
    cE
    @16
    cF
    cH
    cK
    chlt
    cW
    cdlemi.h
    cdlemi.t
    cdlemi.e
    tendovalco
    syl32anc
    @10
    @22
    cG
    cU
    @10
    @22
    cG
    @15
    cF
    ccom
    #
    ccom
    #
    cG
    cG
    @15
    cF
    coass
    @10
    @32
    cG
    cid
    cB
    cres
    #
    ccom
    #
    cG
    @10
    @31
    @33
    cG
    @10
    cB
    cB
    cF
    wf1o
    #
    @31
    @33
    wceq
    @10
    @2
    @4
    @35
    @27
    @29
    cB
    cT
    cF
    cH
    cK
    chlt
    cW
    cdlemi.b
    cdlemi.h
    cdlemi.t
    ltrn1o
    syl2anc
    cB
    cB
    cF
    f1ococnv1
    syl
    coeq2d
    @10
    cB
    cB
    cG
    wf1o
    #
    cB
    cB
    cG
    wf
    @34
    cG
    wceq
    @10
    @2
    @5
    @36
    @27
    @28
    cB
    cT
    cG
    cH
    cK
    chlt
    cW
    cdlemi.b
    cdlemi.h
    cdlemi.t
    ltrn1o
    syl2anc
    cB
    cB
    cG
    f1of
    cB
    cB
    cG
    fcoi1
    3syl
    eqtrd
    syl5eq
    fveq2d
    eqtr3d
    fveq1d
    @10
    @2
    @17
    cT
    wcel
    #
    @13
    cT
    wcel
    #
    @7
    @21
    @18
    wceq
    @27
    @10
    @2
    @3
    @24
    @37
    @27
    @25
    @30
    cU
    cT
    cE
    @16
    cH
    cK
    chlt
    cW
    cdlemi.h
    cdlemi.t
    cdlemi.e
    tendocl
    syl3anc
    @10
    @2
    @3
    @4
    @38
    @27
    @25
    @29
    cU
    cT
    cE
    cF
    cH
    cK
    chlt
    cW
    cdlemi.h
    cdlemi.t
    cdlemi.e
    tendocl
    syl3anc
    #
    @2
    @6
    @7
    @8
    simp3l
    cA
    cP
    cT
    @17
    @13
    cH
    cK
    c.le
    cW
    cdlemi.l
    cdlemi.a
    cdlemi.h
    cdlemi.t
    ltrncoval
    syl121anc
    eqtr3d
    @10
    @2
    @3
    @24
    @14
    cA
    wcel
    @14
    cW
    c.le
    wbr
    wn
    wa
    #
    @18
    @19
    c.le
    wbr
    @27
    @25
    @30
    @2
    @38
    @6
    @9
    @40
    @39
    cA
    cP
    cT
    @13
    cH
    cK
    c.le
    cW
    cdlemi.l
    cdlemi.a
    cdlemi.h
    cdlemi.t
    ltrnel
    syld3an2
    cA
    cB
    @14
    cR
    cT
    cU
    cE
    @16
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemi.b
    cdlemi.l
    cdlemi.j
    cdlemi.m
    cdlemi.a
    cdlemi.h
    cdlemi.t
    cdlemi.r
    cdlemi.e
    cdlemi1
    syl121anc
    eqbrtrd
end
