include "cc0.mm"
include "cpi.mm"
include "cicc.mm"
include "co.mm"
include "wcel.mm"
include "ccos.mm"
include "cfv.mm"
include "wceq.mm"
include "c2.mm"
include "cdiv.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "simplr.mm"
include "wne.mm"
include "csin.mm"
include "cioo.mm"
include "cr.mm"
include "cle.mm"
include "w3a.mm"
include "simpl.mm"
include "0re.mm"
include "pire.mm"
include "elicc2i.mm"
include "sylib.mm"
include "simp1d.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "cxr.mm"
include "wb.mm"
include "rexri.mm"
include "halfpire.mm"
include "elioo2.mm"
include "mp2an.mm"
include "syl3anbrc.mm"
include "sincosq1sgn.mm"
include "syl.mm"
include "simprd.mm"
include "gt0ne0d.mm"
include "c1.mm"
include "cos0.mm"
include "fveq2d.mm"
include "syl5reqr.mm"
include "ax-1ne0.mm"
include "a1i.mm"
include "eqnetrd.mm"
include "wo.mm"
include "simp2d.mm"
include "0red.mm"
include "leloed.mm"
include "mpbid.mm"
include "adantr.mm"
include "mpjaodan.mm"
include "pm2.21ddne.mm"
include "sincosq2sgn.mm"
include "lt0ne0d.mm"
include "cneg.mm"
include "cospi.mm"
include "syl6eq.mm"
include "neg1ne0.mm"
include "simp3d.mm"
include "rehalfcld.mm"
include "lttri4d.mm"
include "mpjao3dan.mm"
include "fveq2.mm"
include "coshalfpi.mm"
include "adantl.mm"
include "impbida.mm"

theorem coseq00topi
  let cA: class A


  assert |- ( A e. ( 0 [,] _pi ) -> ( ( cos ` A ) = 0 <-> A = ( _pi / 2 ) ) )

  proof
    cA
    cc0
    cpi
    cicc
    co
    wcel
    #
    cA
    ccos
    cfv
    #
    cc0
    wceq
    #
    cA
    cpi
    c2
    cdiv
    co
    #
    wceq
    #
    @0
    @2
    wa
    #
    cA
    @3
    clt
    wbr
    #
    @4
    @4
    @3
    cA
    clt
    wbr
    #
    @5
    @6
    wa
    #
    @4
    @1
    cc0
    @0
    @2
    @6
    simplr
    @8
    cc0
    cA
    clt
    wbr
    #
    @1
    cc0
    wne
    #
    cc0
    cA
    wceq
    #
    @8
    @9
    wa
    #
    @1
    @12
    cc0
    cA
    csin
    cfv
    clt
    wbr
    #
    cc0
    @1
    clt
    wbr
    #
    @12
    cA
    cc0
    @3
    cioo
    co
    wcel
    #
    @13
    @14
    wa
    @12
    cA
    cr
    wcel
    #
    @9
    @6
    @15
    @5
    @16
    @6
    @9
    @5
    @16
    cc0
    cA
    cle
    wbr
    #
    cA
    cpi
    cle
    wbr
    #
    @5
    @0
    @16
    @17
    @18
    w3a
    @0
    @2
    simpl
    cc0
    cpi
    cA
    0re
    pire
    elicc2i
    sylib
    #
    simp1d
    #
    ad2antrr
    @8
    @9
    simpr
    @5
    @6
    @9
    simplr
    cc0
    cxr
    wcel
    @3
    cxr
    wcel
    #
    @15
    @16
    @9
    @6
    w3a
    wb
    cc0
    0re
    rexri
    @3
    halfpire
    rexri
    #
    cc0
    @3
    cA
    elioo2
    mp2an
    syl3anbrc
    cA
    sincosq1sgn
    syl
    simprd
    gt0ne0d
    @8
    @11
    wa
    #
    @1
    c1
    cc0
    @23
    c1
    cc0
    ccos
    cfv
    @1
    cos0
    @23
    cc0
    cA
    ccos
    @8
    @11
    simpr
    fveq2d
    syl5reqr
    c1
    cc0
    wne
    @23
    ax-1ne0
    a1i
    eqnetrd
    @5
    @9
    @11
    wo
    #
    @6
    @5
    @17
    @24
    @5
    @16
    @17
    @18
    @19
    simp2d
    @5
    cc0
    cA
    @5
    0red
    @20
    leloed
    mpbid
    adantr
    mpjaodan
    pm2.21ddne
    @5
    @4
    simpr
    @5
    @7
    wa
    #
    @4
    @1
    cc0
    @0
    @2
    @7
    simplr
    @25
    cA
    cpi
    clt
    wbr
    #
    @10
    cA
    cpi
    wceq
    #
    @25
    @26
    wa
    #
    @1
    @28
    @13
    @1
    cc0
    clt
    wbr
    #
    @28
    cA
    @3
    cpi
    cioo
    co
    wcel
    #
    @13
    @29
    wa
    @28
    @16
    @7
    @26
    @30
    @5
    @16
    @7
    @26
    @20
    ad2antrr
    @5
    @7
    @26
    simplr
    @25
    @26
    simpr
    @21
    cpi
    cxr
    wcel
    @30
    @16
    @7
    @26
    w3a
    wb
    @22
    cpi
    pire
    rexri
    @3
    cpi
    cA
    elioo2
    mp2an
    syl3anbrc
    cA
    sincosq2sgn
    syl
    simprd
    lt0ne0d
    @25
    @27
    wa
    #
    @1
    c1
    cneg
    #
    cc0
    @31
    @1
    cpi
    ccos
    cfv
    @32
    @31
    cA
    cpi
    ccos
    @25
    @27
    simpr
    fveq2d
    cospi
    syl6eq
    @32
    cc0
    wne
    @31
    neg1ne0
    a1i
    eqnetrd
    @5
    @26
    @27
    wo
    #
    @7
    @5
    @18
    @33
    @5
    @16
    @17
    @18
    @19
    simp3d
    @5
    cA
    cpi
    @20
    cpi
    cr
    wcel
    @5
    pire
    a1i
    #
    leloed
    mpbid
    adantr
    mpjaodan
    pm2.21ddne
    @5
    cA
    @3
    @20
    @5
    cpi
    @34
    rehalfcld
    lttri4d
    mpjao3dan
    @4
    @2
    @0
    @4
    @1
    @3
    ccos
    cfv
    cc0
    cA
    @3
    ccos
    fveq2
    coshalfpi
    syl6eq
    adantl
    impbida
end
