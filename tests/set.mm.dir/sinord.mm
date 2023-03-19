include "cpi.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cneg.mm"
include "cicc.mm"
include "wcel.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "cmin.mm"
include "ccos.mm"
include "cfv.mm"
include "csin.mm"
include "cr.mm"
include "wb.mm"
include "wss.mm"
include "neghalfpire.mm"
include "halfpire.mm"
include "iccssre.mm"
include "mp2an.mm"
include "sseli.mm"
include "ltsub2.mm"
include "mp3an3.mm"
include "syl2an.mm"
include "cc0.mm"
include "cv.mm"
include "wceq.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "cle.mm"
include "resubcl.mm"
include "sylancr.mm"
include "elicc2i.mm"
include "simp3bi.mm"
include "subge0.mm"
include "mpbird.mm"
include "simp2bi.mm"
include "lesub2.mm"
include "mp3an13.mm"
include "syl.mm"
include "mpbid.mm"
include "caddc.mm"
include "recni.mm"
include "subnegi.mm"
include "pidiv2halves.mm"
include "eqtri.mm"
include "syl6breq.mm"
include "0re.mm"
include "pire.mm"
include "syl3anbrc.mm"
include "vtoclga.mm"
include "cosord.mm"
include "syl2anr.mm"
include "cc.mm"
include "recnd.mm"
include "coshalfpim.mm"
include "breqan12d.mm"
include "3bitrd.mm"

theorem sinord
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A e. ( -u ( _pi / 2 ) [,] ( _pi / 2 ) ) /\ B e. ( -u ( _pi / 2 ) [,] ( _pi / 2 ) ) ) -> ( A < B <-> ( sin ` A ) < ( sin ` B ) ) )

  proof
    cA
    cpi
    c2
    cdiv
    co
    #
    cneg
    #
    @0
    cicc
    co
    #
    wcel
    #
    cB
    @2
    wcel
    #
    wa
    cA
    cB
    clt
    wbr
    #
    @0
    cB
    cmin
    co
    #
    @0
    cA
    cmin
    co
    #
    clt
    wbr
    #
    @7
    ccos
    cfv
    #
    @6
    ccos
    cfv
    #
    clt
    wbr
    #
    cA
    csin
    cfv
    #
    cB
    csin
    cfv
    #
    clt
    wbr
    @3
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    @5
    @8
    wb
    #
    @4
    @2
    cr
    cA
    @1
    cr
    wcel
    #
    @0
    cr
    wcel
    #
    @2
    cr
    wss
    neghalfpire
    halfpire
    @1
    @0
    iccssre
    mp2an
    #
    sseli
    #
    @2
    cr
    cB
    @19
    sseli
    #
    @14
    @15
    @18
    @16
    halfpire
    cA
    cB
    @0
    ltsub2
    mp3an3
    syl2an
    @4
    @6
    cc0
    cpi
    cicc
    co
    #
    wcel
    #
    @7
    @22
    wcel
    #
    @8
    @11
    wb
    @3
    @0
    vx
    cv
    #
    cmin
    co
    #
    @22
    wcel
    #
    @23
    vx
    cB
    @2
    @25
    cB
    wceq
    @26
    @6
    @22
    @25
    cB
    @0
    cmin
    oveq2
    eleq1d
    @25
    @2
    wcel
    #
    @26
    cr
    wcel
    #
    cc0
    @26
    cle
    wbr
    #
    @26
    cpi
    cle
    wbr
    @27
    @28
    @18
    @25
    cr
    wcel
    #
    @29
    halfpire
    @2
    cr
    @25
    @19
    sseli
    #
    @0
    @25
    resubcl
    sylancr
    @28
    @30
    @25
    @0
    cle
    wbr
    #
    @28
    @31
    @1
    @25
    cle
    wbr
    #
    @33
    @1
    @0
    @25
    neghalfpire
    halfpire
    elicc2i
    #
    simp3bi
    @28
    @18
    @31
    @30
    @33
    wb
    halfpire
    @32
    @0
    @25
    subge0
    sylancr
    mpbird
    @28
    @26
    @0
    @1
    cmin
    co
    #
    cpi
    cle
    @28
    @34
    @26
    @36
    cle
    wbr
    #
    @28
    @31
    @34
    @33
    @35
    simp2bi
    @28
    @31
    @34
    @37
    wb
    #
    @32
    @17
    @31
    @18
    @38
    neghalfpire
    halfpire
    @1
    @25
    @0
    lesub2
    mp3an13
    syl
    mpbid
    @36
    @0
    @0
    caddc
    co
    cpi
    @0
    @0
    @0
    halfpire
    recni
    #
    @39
    subnegi
    pidiv2halves
    eqtri
    syl6breq
    cc0
    cpi
    @26
    0re
    pire
    elicc2i
    syl3anbrc
    #
    vtoclga
    @27
    @24
    vx
    cA
    @2
    @25
    cA
    wceq
    @26
    @7
    @22
    @25
    cA
    @0
    cmin
    oveq2
    eleq1d
    @40
    vtoclga
    @6
    @7
    cosord
    syl2anr
    @3
    @4
    @9
    @12
    @10
    @13
    clt
    @3
    cA
    cc
    wcel
    @9
    @12
    wceq
    @3
    cA
    @20
    recnd
    cA
    coshalfpim
    syl
    @4
    cB
    cc
    wcel
    @10
    @13
    wceq
    @4
    cB
    @21
    recnd
    cB
    coshalfpim
    syl
    breqan12d
    3bitrd
end
