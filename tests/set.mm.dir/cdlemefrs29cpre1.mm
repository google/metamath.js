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
include "wreu.mm"
include "wrex.mm"
include "cdlemefrs29bpre1.mm"
include "wb.mm"
include "simp11.mm"
include "simp2rl.mm"
include "atbase.mm"
include "syl.mm"
include "simp2rr.mm"
include "lhpmcvr2.mm"
include "syl12anc.mm"
include "simpl3.mm"
include "pm5.32ri.mm"
include "baibr.mm"
include "cp0.mm"
include "cfv.mm"
include "simp2r.mm"
include "eqid.mm"
include "lhpmat.mm"
include "syl2anc.mm"
include "adantr.mm"
include "oveq2d.mm"
include "col.mm"
include "simp11l.mm"
include "hlol.mm"
include "olj01.mm"
include "syl2an.mm"
include "eqtrd.mm"
include "eqeq1d.mm"
include "anbi2d.mm"
include "3bitr4d.mm"
include "anass.mm"
include "syl6bbr.mm"
include "rexbidva.mm"
include "mpbid.mm"
include "reusv1.mm"
include "mpbird.mm"

theorem cdlemefrs29cpre1
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
  assume cdlemefrs27.rnb: |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( R e. A /\ -. R .<_ W ) ) /\ ps ) -> [_ R / s ]_ N e. B )

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
  disjoint A z
  disjoint B z
  disjoint H z
  disjoint K z
  disjoint .<_ z
  disjoint N z
  disjoint P z
  disjoint Q z
  disjoint R z
  disjoint W z
  disjoint ps z
  disjoint B s
  disjoint .\/ z
  disjoint ./\ s
  disjoint ./\ z
  disjoint ph z
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( R e. A /\ -. R .<_ W ) ) /\ ps ) -> E! z e. B A. s e. A ( ( ( -. s .<_ W /\ ph ) /\ ( s .\/ ( R ./\ W ) ) = R ) -> z = ( N .\/ ( R ./\ W ) ) ) )

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
    wn
    #
    wph
    wa
    @12
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
    cN
    @14
    c.or
    co
    #
    wceq
    wi
    vs
    cA
    wral
    #
    vz
    cB
    wreu
    #
    @19
    vz
    cB
    wrex
    #
    wph
    wps
    vz
    cA
    cB
    cP
    cQ
    cR
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cW
    vs
    cdlemefrs27.b
    cdlemefrs27.l
    cdlemefrs27.j
    cdlemefrs27.m
    cdlemefrs27.a
    cdlemefrs27.h
    cdlemefrs27.eq
    cdlemefrs27.nb
    cdlemefrs27.rnb
    cdlemefrs29bpre1
    @11
    @17
    vs
    cA
    wrex
    #
    @20
    @21
    wb
    @11
    @13
    @16
    wa
    #
    vs
    cA
    wrex
    #
    @22
    @11
    @2
    cR
    cB
    wcel
    #
    @8
    @24
    @2
    @3
    @4
    @10
    wps
    simp11
    #
    @11
    @7
    @25
    @7
    @8
    @6
    @5
    wps
    simp2rl
    cA
    cB
    cR
    cK
    cdlemefrs27.b
    cdlemefrs27.a
    atbase
    syl
    @7
    @8
    @6
    @5
    wps
    simp2rr
    cA
    cB
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cR
    vs
    cdlemefrs27.b
    cdlemefrs27.l
    cdlemefrs27.j
    cdlemefrs27.m
    cdlemefrs27.a
    cdlemefrs27.h
    lhpmcvr2
    syl12anc
    @11
    @23
    @17
    vs
    cA
    @11
    @12
    cA
    wcel
    #
    wa
    #
    @23
    @13
    wph
    @16
    wa
    #
    wa
    @17
    @28
    @16
    @29
    @13
    @28
    @12
    cR
    wceq
    #
    wph
    @30
    wa
    #
    @16
    @29
    @28
    wps
    @30
    @31
    wb
    @5
    @10
    wps
    @27
    simpl3
    @31
    wps
    @30
    @30
    wph
    wps
    cdlemefrs27.eq
    pm5.32ri
    baibr
    syl
    @28
    @15
    @12
    cR
    @28
    @15
    @12
    cK
    cp0
    cfv
    #
    c.or
    co
    #
    @12
    @28
    @14
    @32
    @12
    c.or
    @11
    @14
    @32
    wceq
    #
    @27
    @11
    @2
    @9
    @34
    @26
    @5
    @6
    @9
    wps
    simp2r
    cA
    cR
    cH
    cK
    c.le
    c.an
    cW
    @32
    cdlemefrs27.l
    cdlemefrs27.m
    @32
    eqid
    #
    cdlemefrs27.a
    cdlemefrs27.h
    lhpmat
    syl2anc
    adantr
    oveq2d
    @11
    cK
    col
    wcel
    #
    @12
    cB
    wcel
    @33
    @12
    wceq
    @27
    @11
    @0
    @36
    @0
    @1
    @3
    @4
    @10
    wps
    simp11l
    cK
    hlol
    syl
    cA
    cB
    @12
    cK
    cdlemefrs27.b
    cdlemefrs27.a
    atbase
    cB
    c.or
    cK
    @12
    @32
    cdlemefrs27.b
    cdlemefrs27.j
    @35
    olj01
    syl2an
    eqtrd
    eqeq1d
    #
    @28
    @16
    @30
    wph
    @37
    anbi2d
    3bitr4d
    anbi2d
    @13
    wph
    @16
    anass
    syl6bbr
    rexbidva
    mpbid
    @17
    vz
    vs
    cB
    cA
    @18
    reusv1
    syl
    mpbird
end
