include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wal.mm"
include "csb.mm"
include "df-ral.mm"
include "anass.mm"
include "imbi1i.mm"
include "impexp.mm"
include "3bitr3ri.mm"
include "cp0.mm"
include "cfv.mm"
include "simpl11.mm"
include "simpl2r.mm"
include "eqid.mm"
include "lhpmat.mm"
include "syl2anc.mm"
include "oveq2d.mm"
include "col.mm"
include "simp11l.mm"
include "hlol.mm"
include "syl.mm"
include "adantr.mm"
include "simprl.mm"
include "atbase.mm"
include "olj01.mm"
include "eqtrd.mm"
include "eqeq1d.mm"
include "simpl1.mm"
include "simpl2l.mm"
include "simprr.mm"
include "syl112anc.mm"
include "eqeq2d.mm"
include "imbi12d.mm"
include "pm5.74da.mm"
include "eqcom.mm"
include "imbi2i.mm"
include "simp2rl.mm"
include "simp2rr.mm"
include "simp3.mm"
include "eleq1.mm"
include "breq1.mm"
include "notbid.mm"
include "anbi12d.mm"
include "biimprcd.mm"
include "syl12anc.mm"
include "pm4.71rd.mm"
include "imbi1d.mm"
include "syl5rbbr.mm"
include "syl5bbr.mm"
include "bitrd.mm"
include "syl5bb.mm"
include "albidv.mm"
include "wb.mm"
include "nfcv.mm"
include "csbiebg.mm"
include "syl6bb.mm"

theorem cdlemefrs29bpre0
  let wph: wff ph
  let wps: wff ps
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cW: class W
  let vs: setvar s
  assume cdlemefrs27.b: |- B = ( Base ` K )
  assume cdlemefrs27.l: |- .<_ = ( le ` K )
  assume cdlemefrs27.j: |- .\/ = ( join ` K )
  assume cdlemefrs27.m: |- ./\ = ( meet ` K )
  assume cdlemefrs27.a: |- A = ( Atoms ` K )
  assume cdlemefrs27.h: |- H = ( LHyp ` K )
  assume cdlemefrs27.eq: |- ( s = R -> ( ph <-> ps ) )
  assume cdlemefrs27.nb: |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ P =/= Q /\ ( s e. A /\ ( -. s .<_ W /\ ph ) ) ) -> N e. B )

  disjoint s z
  disjoint A s
  disjoint H s
  disjoint .\/ s
  disjoint K s
  disjoint .<_ s
  disjoint P s
  disjoint Q s
  disjoint R s
  disjoint W s
  disjoint ps s
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( R e. A /\ -. R .<_ W ) ) /\ ps ) -> ( A. s e. A ( ( ( -. s .<_ W /\ ph ) /\ ( s .\/ ( R ./\ W ) ) = R ) -> z = ( N .\/ ( R ./\ W ) ) ) <-> z = [_ R / s ]_ N ) )

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
    cQ
    cA
    wcel
    cQ
    cW
    c.le
    wbr
    wn
    wa
    #
    w3a
    #
    cP
    cQ
    wne
    #
    cR
    cA
    wcel
    #
    cR
    cW
    c.le
    wbr
    #
    wn
    #
    wa
    #
    wa
    #
    wps
    w3a
    #
    vs
    cv
    #
    cW
    c.le
    wbr
    #
    wn
    #
    wph
    wa
    #
    @13
    cR
    cW
    c.an
    co
    #
    c.or
    co
    #
    cR
    wceq
    #
    wa
    #
    vz
    cv
    #
    cN
    @17
    c.or
    co
    #
    wceq
    #
    wi
    #
    vs
    cA
    wral
    #
    @13
    cR
    wceq
    #
    cN
    @21
    wceq
    #
    wi
    #
    vs
    wal
    #
    @21
    vs
    cR
    cN
    csb
    #
    wceq
    #
    @25
    @13
    cA
    wcel
    #
    @24
    wi
    #
    vs
    wal
    @12
    @29
    @24
    vs
    cA
    df-ral
    @12
    @33
    @28
    vs
    @33
    @32
    @16
    wa
    #
    @19
    @23
    wi
    #
    wi
    #
    @12
    @28
    @34
    @19
    wa
    #
    @23
    wi
    @32
    @20
    wa
    #
    @23
    wi
    @36
    @33
    @37
    @38
    @23
    @32
    @16
    @19
    anass
    imbi1i
    @34
    @19
    @23
    impexp
    @32
    @20
    @23
    impexp
    3bitr3ri
    @12
    @36
    @34
    @26
    @21
    cN
    wceq
    #
    wi
    #
    wi
    #
    @28
    @12
    @34
    @35
    @40
    @12
    @34
    wa
    #
    @19
    @26
    @23
    @39
    @42
    @18
    @13
    cR
    @42
    @18
    @13
    cK
    cp0
    cfv
    #
    c.or
    co
    #
    @13
    @42
    @17
    @43
    @13
    c.or
    @42
    @2
    @10
    @17
    @43
    wceq
    @2
    @3
    @4
    @11
    wps
    @34
    simpl11
    @6
    @10
    @5
    wps
    @34
    simpl2r
    cA
    cR
    cH
    cK
    c.le
    c.an
    cW
    @43
    cdlemefrs27.l
    cdlemefrs27.m
    @43
    eqid
    #
    cdlemefrs27.a
    cdlemefrs27.h
    lhpmat
    syl2anc
    #
    oveq2d
    @42
    cK
    col
    wcel
    #
    @13
    cB
    wcel
    #
    @44
    @13
    wceq
    @12
    @47
    @34
    @12
    @0
    @47
    @0
    @1
    @3
    @4
    @11
    wps
    simp11l
    cK
    hlol
    syl
    adantr
    #
    @42
    @32
    @48
    @12
    @32
    @16
    simprl
    #
    cA
    cB
    @13
    cK
    cdlemefrs27.b
    cdlemefrs27.a
    atbase
    syl
    cB
    c.or
    cK
    @13
    @43
    cdlemefrs27.b
    cdlemefrs27.j
    @45
    olj01
    syl2anc
    eqtrd
    eqeq1d
    @42
    @22
    cN
    @21
    @42
    @22
    cN
    @43
    c.or
    co
    #
    cN
    @42
    @17
    @43
    cN
    c.or
    @46
    oveq2d
    @42
    @47
    cN
    cB
    wcel
    #
    @51
    cN
    wceq
    @49
    @42
    @5
    @6
    @32
    @16
    @52
    @5
    @11
    wps
    @34
    simpl1
    @6
    @10
    @5
    wps
    @34
    simpl2l
    @50
    @12
    @32
    @16
    simprr
    cdlemefrs27.nb
    syl112anc
    cB
    c.or
    cK
    cN
    @43
    cdlemefrs27.b
    cdlemefrs27.j
    @45
    olj01
    syl2anc
    eqtrd
    eqeq2d
    imbi12d
    pm5.74da
    @41
    @34
    @26
    wa
    #
    @39
    wi
    #
    @12
    @28
    @34
    @26
    @39
    impexp
    @28
    @40
    @12
    @54
    @39
    @27
    @26
    @21
    cN
    eqcom
    imbi2i
    @12
    @26
    @53
    @39
    @12
    @26
    @34
    @12
    @7
    @9
    wps
    @26
    @34
    wi
    @7
    @9
    @6
    @5
    wps
    simp2rl
    #
    @7
    @9
    @6
    @5
    wps
    simp2rr
    @5
    @11
    wps
    simp3
    @26
    @34
    @7
    @9
    wps
    wa
    #
    wa
    @26
    @32
    @7
    @16
    @56
    @13
    cR
    cA
    eleq1
    @26
    @15
    @9
    wph
    wps
    @26
    @14
    @8
    @13
    cR
    cW
    c.le
    breq1
    notbid
    cdlemefrs27.eq
    anbi12d
    anbi12d
    biimprcd
    syl12anc
    pm4.71rd
    imbi1d
    syl5rbbr
    syl5bbr
    bitrd
    syl5bb
    albidv
    syl5bb
    @12
    @29
    @30
    @21
    wceq
    #
    @31
    @12
    @7
    @29
    @57
    wb
    @55
    vs
    cR
    cN
    @21
    cA
    vs
    @21
    nfcv
    csbiebg
    syl
    @30
    @21
    eqcom
    syl6bb
    bitrd
end
