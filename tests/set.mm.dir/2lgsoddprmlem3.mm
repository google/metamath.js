include "cz.mm"
include "wcel.mm"
include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "c8.mm"
include "cmo.mm"
include "co.mm"
include "wceq.mm"
include "cexp.mm"
include "c1.mm"
include "cmin.mm"
include "cdiv.mm"
include "c7.mm"
include "cpr.mm"
include "wb.mm"
include "wa.mm"
include "c3.mm"
include "c5.mm"
include "cun.mm"
include "lgsdir2lem3.mm"
include "eleq1.mm"
include "eqcoms.mm"
include "wo.mm"
include "wi.mm"
include "elun.mm"
include "elpri.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "2lgsoddprmlem3b.mm"
include "syl6eq.mm"
include "breq2d.mm"
include "n2dvds1.mm"
include "pm2.21i.mm"
include "syl6bi.mm"
include "2lgsoddprmlem3c.mm"
include "breq2i.mm"
include "syl6bb.mm"
include "n2dvds3.mm"
include "jaoi.mm"
include "syl.mm"
include "jao1i.mm"
include "sylbi.mm"
include "cc0.mm"
include "z0even.mm"
include "2lgsoddprmlem3a.mm"
include "syl5breqr.mm"
include "cmul.mm"
include "2z.mm"
include "3z.mm"
include "dvdsmul1.mm"
include "mp2an.mm"
include "2lgsoddprmlem3d.mm"
include "impbid1.mm"
include "syl5com.mm"
include "3impia.mm"

theorem 2lgsoddprmlem3
  let cR: class R
  let cN: class N


  assert |- ( ( N e. ZZ /\ -. 2 || N /\ R = ( N mod 8 ) ) -> ( 2 || ( ( ( R ^ 2 ) - 1 ) / 8 ) <-> R e. { 1 , 7 } ) )

  proof
    cN
    cz
    wcel
    #
    c2
    cN
    cdvds
    wbr
    wn
    #
    cR
    cN
    c8
    cmo
    co
    #
    wceq
    #
    c2
    cR
    c2
    cexp
    co
    #
    c1
    cmin
    co
    #
    c8
    cdiv
    co
    #
    cdvds
    wbr
    #
    cR
    c1
    c7
    cpr
    #
    wcel
    #
    wb
    #
    @0
    @1
    wa
    @2
    @8
    c3
    c5
    cpr
    #
    cun
    #
    wcel
    #
    @3
    @10
    cN
    lgsdir2lem3
    @3
    @13
    cR
    @12
    wcel
    #
    @10
    @13
    @14
    wb
    @2
    cR
    @2
    cR
    @12
    eleq1
    eqcoms
    @14
    @7
    @9
    @14
    @9
    cR
    @11
    wcel
    #
    wo
    @7
    @9
    wi
    #
    cR
    @8
    @11
    elun
    @9
    @15
    @7
    @15
    cR
    c3
    wceq
    #
    cR
    c5
    wceq
    #
    wo
    @16
    cR
    c3
    c5
    elpri
    @17
    @16
    @18
    @17
    @7
    c2
    c1
    cdvds
    wbr
    #
    @9
    @17
    @6
    c1
    c2
    cdvds
    @17
    @6
    c3
    c2
    cexp
    co
    #
    c1
    cmin
    co
    #
    c8
    cdiv
    co
    c1
    @17
    @5
    @21
    c8
    cdiv
    @17
    @4
    @20
    c1
    cmin
    cR
    c3
    c2
    cexp
    oveq1
    oveq1d
    oveq1d
    2lgsoddprmlem3b
    syl6eq
    breq2d
    @19
    @9
    n2dvds1
    pm2.21i
    syl6bi
    @18
    @7
    c2
    c3
    cdvds
    wbr
    #
    @9
    @18
    @7
    c2
    c5
    c2
    cexp
    co
    #
    c1
    cmin
    co
    #
    c8
    cdiv
    co
    #
    cdvds
    wbr
    @22
    @18
    @6
    @25
    c2
    cdvds
    @18
    @5
    @24
    c8
    cdiv
    @18
    @4
    @23
    c1
    cmin
    cR
    c5
    c2
    cexp
    oveq1
    oveq1d
    oveq1d
    breq2d
    @25
    c3
    c2
    cdvds
    2lgsoddprmlem3c
    breq2i
    syl6bb
    @22
    @9
    n2dvds3
    pm2.21i
    syl6bi
    jaoi
    syl
    jao1i
    sylbi
    @9
    cR
    c1
    wceq
    #
    cR
    c7
    wceq
    #
    wo
    @7
    cR
    c1
    c7
    elpri
    @26
    @7
    @27
    @26
    c2
    cc0
    @6
    cdvds
    z0even
    @26
    @6
    c1
    c2
    cexp
    co
    #
    c1
    cmin
    co
    #
    c8
    cdiv
    co
    cc0
    @26
    @5
    @29
    c8
    cdiv
    @26
    @4
    @28
    c1
    cmin
    cR
    c1
    c2
    cexp
    oveq1
    oveq1d
    oveq1d
    2lgsoddprmlem3a
    syl6eq
    syl5breqr
    @27
    c2
    c2
    c3
    cmul
    co
    #
    @6
    cdvds
    c2
    cz
    wcel
    c3
    cz
    wcel
    c2
    @30
    cdvds
    wbr
    2z
    3z
    c2
    c3
    dvdsmul1
    mp2an
    @27
    @6
    c7
    c2
    cexp
    co
    #
    c1
    cmin
    co
    #
    c8
    cdiv
    co
    @30
    @27
    @5
    @32
    c8
    cdiv
    @27
    @4
    @31
    c1
    cmin
    cR
    c7
    c2
    cexp
    oveq1
    oveq1d
    oveq1d
    2lgsoddprmlem3d
    syl6eq
    syl5breqr
    jaoi
    syl
    impbid1
    syl6bi
    syl5com
    3impia
end
