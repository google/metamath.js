include "cc0.mm"
include "cpi.mm"
include "cioo.mm"
include "co.mm"
include "wcel.mm"
include "cr.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "csin.mm"
include "cfv.mm"
include "cxr.mm"
include "wb.mm"
include "0xr.mm"
include "pire.mm"
include "rexri.mm"
include "elioo2.mm"
include "mp2an.mm"
include "c2.mm"
include "cdiv.mm"
include "ccos.mm"
include "cmul.mm"
include "rehalfcl.mm"
include "3ad2ant1.mm"
include "halfpos2.mm"
include "biimpa.mm"
include "3adant3.mm"
include "wa.mm"
include "2re.mm"
include "2pos.mm"
include "pm3.2i.mm"
include "ltdiv1.mm"
include "mp3an23.mm"
include "adantr.mm"
include "biimp3a.mm"
include "sincosq1lem.mm"
include "syl3anc.mm"
include "cmin.mm"
include "resubcl.mm"
include "mpan.mm"
include "syl.mm"
include "posdif.mm"
include "mpan2.mm"
include "bitrd.mm"
include "ltsubpos.mm"
include "wceq.mm"
include "cc.mm"
include "recn.mm"
include "wne.mm"
include "picn.mm"
include "2cnne0.mm"
include "divsubdir.mm"
include "mp3an13.mm"
include "fveq2d.mm"
include "recnd.mm"
include "sinhalfpim.mm"
include "eqtrd.mm"
include "breqtrd.mm"
include "wi.mm"
include "resincl.mm"
include "recoscl.mm"
include "jca.mm"
include "axmulgt0.mm"
include "3syl.mm"
include "remulcl.mm"
include "sylancr.mm"
include "mpani.mm"
include "syld.mm"
include "mp2and.mm"
include "2cn.mm"
include "2ne0.mm"
include "divcan2.mm"
include "sin2t.mm"
include "eqtr3d.mm"
include "breqtrrd.mm"
include "sylbi.mm"

theorem sinq12gt0
  let cA: class A


  assert |- ( A e. ( 0 (,) _pi ) -> 0 < ( sin ` A ) )

  proof
    cA
    cc0
    cpi
    cioo
    co
    wcel
    #
    cA
    cr
    wcel
    #
    cc0
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
    cc0
    cxr
    wcel
    cpi
    cxr
    wcel
    @0
    @4
    wb
    0xr
    cpi
    pire
    rexri
    cc0
    cpi
    cA
    elioo2
    mp2an
    @4
    cc0
    c2
    cA
    c2
    cdiv
    co
    #
    csin
    cfv
    #
    @6
    ccos
    cfv
    #
    cmul
    co
    #
    cmul
    co
    #
    @5
    clt
    @4
    cc0
    @7
    clt
    wbr
    #
    cc0
    @8
    clt
    wbr
    #
    cc0
    @10
    clt
    wbr
    #
    @4
    @6
    cr
    wcel
    #
    cc0
    @6
    clt
    wbr
    #
    @6
    cpi
    c2
    cdiv
    co
    #
    clt
    wbr
    #
    @11
    @1
    @2
    @14
    @3
    cA
    rehalfcl
    #
    3ad2ant1
    @1
    @2
    @15
    @3
    @1
    @2
    @15
    cA
    halfpos2
    biimpa
    3adant3
    @1
    @2
    @3
    @17
    @1
    @3
    @17
    wb
    #
    @2
    @1
    cpi
    cr
    wcel
    #
    c2
    cr
    wcel
    #
    cc0
    c2
    clt
    wbr
    #
    wa
    #
    @19
    pire
    @21
    @22
    2re
    2pos
    pm3.2i
    #
    cA
    cpi
    c2
    ltdiv1
    mp3an23
    adantr
    biimp3a
    @6
    sincosq1lem
    syl3anc
    @4
    cc0
    cpi
    cA
    cmin
    co
    #
    c2
    cdiv
    co
    #
    csin
    cfv
    #
    @8
    clt
    @4
    @26
    cr
    wcel
    #
    cc0
    @26
    clt
    wbr
    #
    @26
    @16
    clt
    wbr
    #
    cc0
    @27
    clt
    wbr
    @1
    @2
    @28
    @3
    @1
    @25
    cr
    wcel
    #
    @28
    @20
    @1
    @31
    pire
    cpi
    cA
    resubcl
    mpan
    #
    @25
    rehalfcl
    syl
    3ad2ant1
    @1
    @2
    @3
    @29
    @1
    @3
    @29
    wb
    @2
    @1
    @3
    cc0
    @25
    clt
    wbr
    #
    @29
    @1
    @20
    @3
    @33
    wb
    pire
    cA
    cpi
    posdif
    mpan2
    @1
    @31
    @33
    @29
    wb
    @32
    @25
    halfpos2
    syl
    bitrd
    adantr
    biimp3a
    @1
    @2
    @30
    @3
    @1
    @2
    @30
    @1
    @2
    @25
    cpi
    clt
    wbr
    #
    @30
    @1
    @20
    @2
    @34
    wb
    pire
    cA
    cpi
    ltsubpos
    mpan2
    @1
    @31
    @34
    @30
    wb
    #
    @32
    @31
    @20
    @23
    @35
    pire
    @24
    @25
    cpi
    c2
    ltdiv1
    mp3an23
    syl
    bitrd
    biimpa
    3adant3
    @26
    sincosq1lem
    syl3anc
    @1
    @2
    @27
    @8
    wceq
    @3
    @1
    @27
    @16
    @6
    cmin
    co
    #
    csin
    cfv
    #
    @8
    @1
    @26
    @36
    csin
    @1
    cA
    cc
    wcel
    #
    @26
    @36
    wceq
    #
    cA
    recn
    #
    cpi
    cc
    wcel
    @38
    c2
    cc
    wcel
    #
    c2
    cc0
    wne
    #
    wa
    @39
    picn
    2cnne0
    cpi
    cA
    c2
    divsubdir
    mp3an13
    syl
    fveq2d
    @1
    @6
    cc
    wcel
    #
    @37
    @8
    wceq
    @1
    @6
    @18
    recnd
    #
    @6
    sinhalfpim
    syl
    eqtrd
    3ad2ant1
    breqtrd
    @1
    @2
    @11
    @12
    wa
    #
    @13
    wi
    @3
    @1
    @45
    cc0
    @9
    clt
    wbr
    #
    @13
    @1
    @14
    @7
    cr
    wcel
    #
    @8
    cr
    wcel
    #
    wa
    #
    @45
    @46
    wi
    @18
    @14
    @47
    @48
    @6
    resincl
    @6
    recoscl
    jca
    #
    @7
    @8
    axmulgt0
    3syl
    @1
    @22
    @46
    @13
    2pos
    @1
    @21
    @9
    cr
    wcel
    #
    @22
    @46
    wa
    @13
    wi
    2re
    @1
    @14
    @49
    @51
    @18
    @50
    @7
    @8
    remulcl
    3syl
    c2
    @9
    axmulgt0
    sylancr
    mpani
    syld
    3ad2ant1
    mp2and
    @1
    @2
    @5
    @10
    wceq
    @3
    @1
    c2
    @6
    cmul
    co
    #
    csin
    cfv
    #
    @5
    @10
    @1
    @52
    cA
    csin
    @1
    @38
    @52
    cA
    wceq
    #
    @40
    @38
    @41
    @42
    @54
    2cn
    2ne0
    cA
    c2
    divcan2
    mp3an23
    syl
    fveq2d
    @1
    @43
    @53
    @10
    wceq
    @44
    @6
    sin2t
    syl
    eqtr3d
    3ad2ant1
    breqtrrd
    sylbi
end
