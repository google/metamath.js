include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "w3a.mm"
include "wne.mm"
include "cid.mm"
include "cres.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "ccnv.mm"
include "ccom.mm"
include "cv.mm"
include "crio.mm"
include "simp13.mm"
include "cdlemksv.mm"
include "syl.mm"
include "eqcomd.mm"
include "wreu.mm"
include "wb.mm"
include "cdlemkuel.mm"
include "simp11l.mm"
include "simp11r.mm"
include "simp33.mm"
include "cdlemk16a.mm"
include "cdleme.mm"
include "syl211anc.mm"
include "cmpt.mm"
include "nfcv.mm"
include "nfriota1.mm"
include "nfmpt.mm"
include "nfcxfr.mm"
include "nffv.mm"
include "nfeq1.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "riota2f.mm"
include "syl2anc.mm"
include "mpbird.mm"

theorem cdlemkuv2
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let ve: setvar e
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cO: class O
  let cW: class W
  assume cdlemk1.b: |- B = ( Base ` K )
  assume cdlemk1.l: |- .<_ = ( le ` K )
  assume cdlemk1.j: |- .\/ = ( join ` K )
  assume cdlemk1.m: |- ./\ = ( meet ` K )
  assume cdlemk1.a: |- A = ( Atoms ` K )
  assume cdlemk1.h: |- H = ( LHyp ` K )
  assume cdlemk1.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemk1.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemk1.s: |- S = ( f e. T |-> ( iota_ i e. T ( i ` P ) = ( ( P .\/ ( R ` f ) ) ./\ ( ( N ` P ) .\/ ( R ` ( f o. `' F ) ) ) ) ) )
  assume cdlemk1.o: |- O = ( S ` D )
  assume cdlemk1.u: |- U = ( e e. T |-> ( iota_ j e. T ( j ` P ) = ( ( P .\/ ( R ` e ) ) ./\ ( ( O ` P ) .\/ ( R ` ( e o. `' D ) ) ) ) ) )

  disjoint f i
  disjoint ./\ f
  disjoint ./\ i
  disjoint .<_ i
  disjoint .\/ f
  disjoint .\/ i
  disjoint A i
  disjoint D f
  disjoint D i
  disjoint F f
  disjoint F i
  disjoint H i
  disjoint K i
  disjoint N f
  disjoint N i
  disjoint P f
  disjoint P i
  disjoint R f
  disjoint R i
  disjoint T f
  disjoint T i
  disjoint W f
  disjoint W i
  disjoint ./\ e
  disjoint .\/ e
  disjoint D e
  disjoint e j
  disjoint G e
  disjoint G j
  disjoint O e
  disjoint P e
  disjoint R e
  disjoint T e
  disjoint W e
  disjoint ./\ j
  disjoint .<_ j
  disjoint .\/ j
  disjoint A j
  disjoint D j
  disjoint F j
  disjoint H j
  disjoint K j
  disjoint N j
  disjoint O j
  disjoint P j
  disjoint R j
  disjoint T j
  disjoint W j
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( R ` F ) = ( R ` N ) /\ G e. T ) /\ ( F e. T /\ D e. T /\ N e. T ) /\ ( ( ( R ` D ) =/= ( R ` F ) /\ ( R ` D ) =/= ( R ` G ) ) /\ ( F =/= ( _I |` B ) /\ G =/= ( _I |` B ) /\ D =/= ( _I |` B ) ) /\ ( P e. A /\ -. P .<_ W ) ) ) -> ( ( U ` G ) ` P ) = ( ( P .\/ ( R ` G ) ) ./\ ( ( O ` P ) .\/ ( R ` ( G o. `' D ) ) ) ) )

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
    cR
    cfv
    #
    cN
    cR
    cfv
    wceq
    #
    cG
    cT
    wcel
    #
    w3a
    #
    cF
    cT
    wcel
    cD
    cT
    wcel
    cN
    cT
    wcel
    w3a
    #
    cD
    cR
    cfv
    #
    @3
    wne
    @8
    cG
    cR
    cfv
    #
    wne
    wa
    #
    cF
    cid
    cB
    cres
    #
    wne
    cG
    @11
    wne
    cD
    @11
    wne
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
    w3a
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
    @9
    c.or
    co
    cP
    cO
    cfv
    #
    cG
    cD
    ccnv
    #
    ccom
    cR
    cfv
    c.or
    co
    c.an
    co
    #
    wceq
    #
    cP
    vj
    cv
    #
    cfv
    #
    @20
    wceq
    #
    vj
    cT
    crio
    #
    @16
    wceq
    #
    @15
    @16
    @25
    @15
    @5
    @16
    @25
    wceq
    @2
    @4
    @5
    @7
    @14
    simp13
    cA
    cB
    cP
    cR
    cU
    cT
    ve
    vj
    cD
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cO
    cW
    cdlemk1.b
    cdlemk1.l
    cdlemk1.j
    cdlemk1.a
    cdlemk1.h
    cdlemk1.t
    cdlemk1.r
    cdlemk1.m
    cdlemk1.u
    cdlemksv
    syl
    eqcomd
    @15
    @16
    cT
    wcel
    @24
    vj
    cT
    wreu
    #
    @21
    @26
    wb
    cA
    cB
    cD
    cP
    cR
    cS
    cT
    cU
    ve
    vf
    vi
    vj
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cO
    cW
    cdlemk1.b
    cdlemk1.l
    cdlemk1.j
    cdlemk1.m
    cdlemk1.a
    cdlemk1.h
    cdlemk1.t
    cdlemk1.r
    cdlemk1.s
    cdlemk1.o
    cdlemk1.u
    cdlemkuel
    @15
    @0
    @1
    @13
    @20
    cA
    wcel
    @20
    cW
    c.le
    wbr
    wn
    wa
    @27
    @0
    @1
    @4
    @5
    @7
    @14
    simp11l
    @0
    @1
    @4
    @5
    @7
    @14
    simp11r
    @6
    @7
    @10
    @12
    @13
    simp33
    cA
    cB
    cD
    cP
    cR
    cS
    cT
    vf
    vi
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cO
    cW
    cdlemk1.b
    cdlemk1.l
    cdlemk1.j
    cdlemk1.m
    cdlemk1.a
    cdlemk1.h
    cdlemk1.t
    cdlemk1.r
    cdlemk1.s
    cdlemk1.o
    cdlemk16a
    cA
    cP
    @20
    cT
    vj
    cH
    cK
    c.le
    cW
    cdlemk1.l
    cdlemk1.a
    cdlemk1.h
    cdlemk1.t
    cdleme
    syl211anc
    @24
    @21
    vj
    cT
    @16
    vj
    cG
    cU
    vj
    cU
    ve
    cT
    @23
    cP
    ve
    cv
    #
    cR
    cfv
    c.or
    co
    @18
    @28
    @19
    ccom
    cR
    cfv
    c.or
    co
    c.an
    co
    wceq
    #
    vj
    cT
    crio
    #
    cmpt
    cdlemk1.u
    vj
    ve
    cT
    @30
    vj
    cT
    nfcv
    @29
    vj
    cT
    nfriota1
    nfmpt
    nfcxfr
    vj
    cG
    nfcv
    nffv
    #
    vj
    @17
    @20
    vj
    cP
    @16
    @31
    vj
    cP
    nfcv
    nffv
    nfeq1
    @22
    @16
    wceq
    @23
    @17
    @20
    cP
    @22
    @16
    fveq1
    eqeq1d
    riota2f
    syl2anc
    mpbird
end
