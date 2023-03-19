include "cpi.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cioo.mm"
include "wcel.mm"
include "cr.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cc0.mm"
include "csin.mm"
include "cfv.mm"
include "ccos.mm"
include "wa.mm"
include "wb.mm"
include "halfpire.mm"
include "pire.mm"
include "cxr.mm"
include "rexr.mm"
include "elioo2.mm"
include "syl2an.mm"
include "mp2an.mm"
include "cmin.mm"
include "cneg.mm"
include "resubcl.mm"
include "mpan2.mm"
include "0xr.mm"
include "rexri.mm"
include "sincosq1sgn.mm"
include "sylbir.mm"
include "syl3an1.mm"
include "3expib.mm"
include "0re.mm"
include "ltsub13.mm"
include "mp3an13.mm"
include "recn.mm"
include "subid1d.mm"
include "breq2d.mm"
include "bitrd.mm"
include "caddc.mm"
include "ltsubadd.mm"
include "mp3an23.mm"
include "pidiv2halves.mm"
include "breq2i.mm"
include "syl6bb.mm"
include "anbi12d.mm"
include "resincld.mm"
include "lt0neg2d.mm"
include "anbi1d.mm"
include "3imtr3d.mm"
include "cc.mm"
include "wceq.mm"
include "recni.mm"
include "pncan3.mm"
include "sylancr.mm"
include "fveq2d.mm"
include "recnd.mm"
include "coshalfpip.mm"
include "syl.mm"
include "eqtr3d.mm"
include "breq1d.mm"
include "sinhalfpip.mm"
include "sylibrd.mm"
include "3impib.mm"
include "ancomd.mm"
include "sylbi.mm"

theorem sincosq2sgn
  let cA: class A


  assert |- ( A e. ( ( _pi / 2 ) (,) _pi ) -> ( 0 < ( sin ` A ) /\ ( cos ` A ) < 0 ) )

  proof
    cA
    cpi
    c2
    cdiv
    co
    #
    cpi
    cioo
    co
    wcel
    #
    cA
    cr
    wcel
    #
    @0
    cA
    clt
    wbr
    #
    cA
    cpi
    clt
    wbr
    #
    w3a
    #
    cc0
    cA
    csin
    cfv
    #
    clt
    wbr
    #
    cA
    ccos
    cfv
    #
    cc0
    clt
    wbr
    #
    wa
    @0
    cr
    wcel
    #
    cpi
    cr
    wcel
    #
    @1
    @5
    wb
    #
    halfpire
    pire
    @10
    @0
    cxr
    wcel
    #
    cpi
    cxr
    wcel
    @12
    @11
    @0
    rexr
    cpi
    rexr
    @0
    cpi
    cA
    elioo2
    syl2an
    mp2an
    @5
    @9
    @7
    @2
    @3
    @4
    @9
    @7
    wa
    #
    @2
    @3
    @4
    wa
    #
    cA
    @0
    cmin
    co
    #
    csin
    cfv
    #
    cneg
    #
    cc0
    clt
    wbr
    #
    cc0
    @16
    ccos
    cfv
    #
    clt
    wbr
    #
    wa
    #
    @14
    @2
    cc0
    @16
    clt
    wbr
    #
    @16
    @0
    clt
    wbr
    #
    wa
    cc0
    @17
    clt
    wbr
    #
    @21
    wa
    #
    @15
    @22
    @2
    @23
    @24
    @26
    @2
    @16
    cr
    wcel
    #
    @23
    @24
    @26
    @2
    @10
    @27
    halfpire
    cA
    @0
    resubcl
    mpan2
    #
    @27
    @23
    @24
    w3a
    #
    @16
    cc0
    @0
    cioo
    co
    wcel
    #
    @26
    cc0
    cxr
    wcel
    @13
    @30
    @29
    wb
    0xr
    @0
    halfpire
    rexri
    cc0
    @0
    @16
    elioo2
    mp2an
    @16
    sincosq1sgn
    sylbir
    syl3an1
    3expib
    @2
    @23
    @3
    @24
    @4
    @2
    @23
    @0
    cA
    cc0
    cmin
    co
    #
    clt
    wbr
    #
    @3
    cc0
    cr
    wcel
    @2
    @10
    @23
    @32
    wb
    0re
    halfpire
    cc0
    cA
    @0
    ltsub13
    mp3an13
    @2
    @31
    cA
    @0
    clt
    @2
    cA
    cA
    recn
    #
    subid1d
    breq2d
    bitrd
    @2
    @24
    cA
    @0
    @0
    caddc
    co
    #
    clt
    wbr
    #
    @4
    @2
    @10
    @10
    @24
    @35
    wb
    halfpire
    halfpire
    cA
    @0
    @0
    ltsubadd
    mp3an23
    @34
    cpi
    cA
    clt
    pidiv2halves
    breq2i
    syl6bb
    anbi12d
    @2
    @25
    @19
    @21
    @2
    @17
    @2
    @16
    @28
    resincld
    lt0neg2d
    anbi1d
    3imtr3d
    @2
    @9
    @19
    @7
    @21
    @2
    @8
    @18
    cc0
    clt
    @2
    @0
    @16
    caddc
    co
    #
    ccos
    cfv
    #
    @8
    @18
    @2
    @36
    cA
    ccos
    @2
    @0
    cc
    wcel
    cA
    cc
    wcel
    @36
    cA
    wceq
    @0
    halfpire
    recni
    @33
    @0
    cA
    pncan3
    sylancr
    #
    fveq2d
    @2
    @16
    cc
    wcel
    #
    @37
    @18
    wceq
    @2
    @16
    @28
    recnd
    #
    @16
    coshalfpip
    syl
    eqtr3d
    breq1d
    @2
    @6
    @20
    cc0
    clt
    @2
    @36
    csin
    cfv
    #
    @6
    @20
    @2
    @36
    cA
    csin
    @38
    fveq2d
    @2
    @39
    @41
    @20
    wceq
    @40
    @16
    sinhalfpip
    syl
    eqtr3d
    breq2d
    anbi12d
    sylibrd
    3impib
    ancomd
    sylbi
end
