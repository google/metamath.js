include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wb.mm"
include "simpl3.mm"
include "pm5.32ri.mm"
include "baibr.mm"
include "syl.mm"
include "cp0.mm"
include "cfv.mm"
include "eqid.mm"
include "lhpmat.mm"
include "3adant3.mm"
include "adantr.mm"
include "oveq2d.mm"
include "col.mm"
include "simpl1l.mm"
include "hlol.mm"
include "atbase.mm"
include "adantl.mm"
include "olj01.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "eqeq1d.mm"
include "anbi2d.mm"
include "3bitr4d.mm"
include "anass.mm"
include "syl6rbbr.mm"

theorem cdlemefrs29pre00
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  let cR: class R
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let vs: setvar s
  assume cdlemefrs29.b: |- B = ( Base ` K )
  assume cdlemefrs29.l: |- .<_ = ( le ` K )
  assume cdlemefrs29.j: |- .\/ = ( join ` K )
  assume cdlemefrs29.m: |- ./\ = ( meet ` K )
  assume cdlemefrs29.a: |- A = ( Atoms ` K )
  assume cdlemefrs29.h: |- H = ( LHyp ` K )
  assume cdlemefrs29.eq: |- ( s = R -> ( ph <-> ps ) )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( R e. A /\ -. R .<_ W ) /\ ps ) /\ s e. A ) -> ( ( ( -. s .<_ W /\ ph ) /\ ( s .\/ ( R ./\ W ) ) = R ) <-> ( -. s .<_ W /\ ( s .\/ ( R ./\ W ) ) = R ) ) )

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
    cR
    cA
    wcel
    cR
    cW
    c.le
    wbr
    wn
    wa
    #
    wps
    w3a
    #
    vs
    cv
    #
    cA
    wcel
    #
    wa
    #
    @5
    cW
    c.le
    wbr
    wn
    #
    @5
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
    @8
    wph
    @11
    wa
    #
    wa
    @8
    wph
    wa
    @11
    wa
    @7
    @11
    @12
    @8
    @7
    @5
    cR
    wceq
    #
    wph
    @13
    wa
    #
    @11
    @12
    @7
    wps
    @13
    @14
    wb
    @2
    @3
    wps
    @6
    simpl3
    @14
    wps
    @13
    @13
    wph
    wps
    cdlemefrs29.eq
    pm5.32ri
    baibr
    syl
    @7
    @10
    @5
    cR
    @7
    @10
    @5
    cK
    cp0
    cfv
    #
    c.or
    co
    #
    @5
    @7
    @9
    @15
    @5
    c.or
    @4
    @9
    @15
    wceq
    #
    @6
    @2
    @3
    @17
    wps
    cA
    cR
    cH
    cK
    c.le
    c.an
    cW
    @15
    cdlemefrs29.l
    cdlemefrs29.m
    @15
    eqid
    #
    cdlemefrs29.a
    cdlemefrs29.h
    lhpmat
    3adant3
    adantr
    oveq2d
    @7
    cK
    col
    wcel
    #
    @5
    cB
    wcel
    #
    @16
    @5
    wceq
    @7
    @0
    @19
    @0
    @1
    @3
    wps
    @6
    simpl1l
    cK
    hlol
    syl
    @6
    @20
    @4
    cA
    cB
    @5
    cK
    cdlemefrs29.b
    cdlemefrs29.a
    atbase
    adantl
    cB
    c.or
    cK
    @5
    @15
    cdlemefrs29.b
    cdlemefrs29.j
    @18
    olj01
    syl2anc
    eqtrd
    eqeq1d
    #
    @7
    @11
    @13
    wph
    @21
    anbi2d
    3bitr4d
    anbi2d
    @8
    wph
    @11
    anass
    syl6rbbr
end
