include "chlt.mm"
include "wcel.mm"
include "co.mm"
include "wbr.mm"
include "cv.mm"
include "wn.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "w3a.mm"
include "wne.mm"
include "wo.mm"
include "simp3r.mm"
include "simp12.mm"
include "jca.mm"
include "wi.mm"
include "wral.mm"
include "simp3l.mm"
include "simp13.mm"
include "ralnex.mm"
include "sylibr.mm"
include "breq1.mm"
include "notbid.mm"
include "oveq2.mm"
include "eqeq12d.mm"
include "anbi12d.mm"
include "rspcva.mm"
include "syl2anc.mm"
include "clc.mm"
include "wb.mm"
include "simp11.mm"
include "hlcvl.mm"
include "syl.mm"
include "simp21.mm"
include "simp22.mm"
include "simp23.mm"
include "cvlsupr2.mm"
include "syl131anc.mm"
include "anbi2d.mm"
include "mtbid.mm"
include "ianor.mm"
include "df-3an.mm"
include "anbi2i.mm"
include "an12.mm"
include "bitri.mm"
include "notbii.mm"
include "pm4.62.mm"
include "3bitr4ri.mm"
include "mt2d.mm"
include "neanior.mm"
include "con2bii.mm"

theorem cdleme0nex
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let vr: setvar r
  assume cdleme0nex.l: |- .<_ = ( le ` K )
  assume cdleme0nex.j: |- .\/ = ( join ` K )
  assume cdleme0nex.a: |- A = ( Atoms ` K )

  disjoint A r
  disjoint .\/ r
  disjoint .<_ r
  disjoint P r
  disjoint Q r
  disjoint R r
  disjoint W r
  assert |- ( ( ( K e. HL /\ R .<_ ( P .\/ Q ) /\ -. E. r e. A ( -. r .<_ W /\ ( P .\/ r ) = ( Q .\/ r ) ) ) /\ ( P e. A /\ Q e. A /\ P =/= Q ) /\ ( R e. A /\ -. R .<_ W ) ) -> ( R = P \/ R = Q ) )

  proof
    cK
    chlt
    wcel
    #
    cR
    cP
    cQ
    c.or
    co
    c.le
    wbr
    #
    vr
    cv
    #
    cW
    c.le
    wbr
    #
    wn
    #
    cP
    @2
    c.or
    co
    #
    cQ
    @2
    c.or
    co
    #
    wceq
    #
    wa
    #
    vr
    cA
    wrex
    wn
    #
    w3a
    #
    cP
    cA
    wcel
    #
    cQ
    cA
    wcel
    #
    cP
    cQ
    wne
    #
    w3a
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
    w3a
    #
    cR
    cP
    wne
    #
    cR
    cQ
    wne
    #
    wa
    #
    wn
    #
    cR
    cP
    wceq
    cR
    cQ
    wceq
    wo
    #
    @19
    @22
    @17
    @1
    wa
    #
    @19
    @17
    @1
    @10
    @14
    @15
    @17
    simp3r
    @0
    @1
    @9
    @14
    @18
    simp12
    jca
    @19
    @17
    @20
    @21
    @1
    w3a
    #
    wa
    #
    wn
    #
    @22
    @25
    wn
    #
    wi
    #
    @19
    @17
    cP
    cR
    c.or
    co
    #
    cQ
    cR
    c.or
    co
    #
    wceq
    #
    wa
    #
    @27
    @19
    @15
    @8
    wn
    #
    vr
    cA
    wral
    #
    @34
    wn
    #
    @10
    @14
    @15
    @17
    simp3l
    #
    @19
    @9
    @36
    @0
    @1
    @9
    @14
    @18
    simp13
    @8
    vr
    cA
    ralnex
    sylibr
    @35
    @37
    vr
    cR
    cA
    @2
    cR
    wceq
    #
    @8
    @34
    @39
    @4
    @17
    @7
    @33
    @39
    @3
    @16
    @2
    cR
    cW
    c.le
    breq1
    notbid
    @39
    @5
    @31
    @6
    @32
    @2
    cR
    cP
    c.or
    oveq2
    @2
    cR
    cQ
    c.or
    oveq2
    eqeq12d
    anbi12d
    notbid
    rspcva
    syl2anc
    @19
    @33
    @26
    @17
    @19
    cK
    clc
    wcel
    #
    @11
    @12
    @15
    @13
    @33
    @26
    wb
    @19
    @0
    @40
    @0
    @1
    @9
    @14
    @18
    simp11
    cK
    hlcvl
    syl
    @10
    @11
    @12
    @13
    @18
    simp21
    @10
    @11
    @12
    @13
    @18
    simp22
    @38
    @10
    @11
    @12
    @13
    @18
    simp23
    cA
    cP
    cQ
    cR
    c.or
    cK
    c.le
    cdleme0nex.a
    cdleme0nex.l
    cdleme0nex.j
    cvlsupr2
    syl131anc
    anbi2d
    mtbid
    @22
    @25
    wa
    #
    wn
    @23
    @29
    wo
    @28
    @30
    @22
    @25
    ianor
    @27
    @41
    @27
    @17
    @22
    @1
    wa
    #
    wa
    @41
    @26
    @42
    @17
    @20
    @21
    @1
    df-3an
    anbi2i
    @17
    @22
    @1
    an12
    bitri
    notbii
    @22
    @25
    pm4.62
    3bitr4ri
    sylibr
    mt2d
    @22
    @24
    cR
    cP
    cR
    cQ
    neanior
    con2bii
    sylibr
end
