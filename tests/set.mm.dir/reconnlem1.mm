include "cr.mm"
include "wss.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "crest.mm"
include "co.mm"
include "cconn.mm"
include "wcel.mm"
include "wa.mm"
include "cicc.mm"
include "cdif.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "simplr.mm"
include "wn.mm"
include "cmnf.mm"
include "cpnf.mm"
include "ctopon.mm"
include "retopon.mm"
include "a1i.mm"
include "simplll.mm"
include "iooretop.mm"
include "cin.mm"
include "wne.mm"
include "clt.mm"
include "wbr.mm"
include "simplrl.mm"
include "sseldd.mm"
include "mnflt.mm"
include "syl.mm"
include "eldifn.mm"
include "adantl.mm"
include "eleq1.mm"
include "syl5ibcom.mm"
include "mtod.mm"
include "cle.mm"
include "wo.mm"
include "w3a.mm"
include "eldifi.mm"
include "wb.mm"
include "simplrr.mm"
include "elicc2.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "simp2d.mm"
include "simp1d.mm"
include "leloed.mm"
include "ord.mm"
include "mt3d.mm"
include "cxr.mm"
include "mnfxr.mm"
include "rexrd.mm"
include "elioo2.mm"
include "sylancr.mm"
include "mpbir3and.mm"
include "inelcm.mm"
include "syl5ibrcom.mm"
include "simp3d.mm"
include "ltpnf.mm"
include "pnfxr.mm"
include "sylancl.mm"
include "inss1.mm"
include "jctil.mm"
include "jctir.mm"
include "leidd.mm"
include "ioodisj.mm"
include "syl21anc.mm"
include "sseq0.mm"
include "csn.mm"
include "cun.mm"
include "ioojoin.mm"
include "syl32anc.mm"
include "unass.mm"
include "un12.mm"
include "eqtri.mm"
include "ioomax.mm"
include "3eqtr3g.mm"
include "sseqtr4d.mm"
include "disjsn.mm"
include "sylibr.mm"
include "disjssun.mm"
include "nconnsubb.mm"
include "ex.mm"
include "mt2d.mm"
include "eq0rdv.mm"
include "ssdif0.mm"

theorem reconnlem1
  let cA: class A
  let cX: class X
  let cY: class Y
  let vz: setvar z


  assert |- ( ( ( A C_ RR /\ ( ( topGen ` ran (,) ) |`t A ) e. Conn ) /\ ( X e. A /\ Y e. A ) ) -> ( X [,] Y ) C_ A )

  proof
    cA
    cr
    wss
    #
    cioo
    crn
    ctg
    cfv
    #
    cA
    crest
    co
    cconn
    wcel
    #
    wa
    #
    cX
    cA
    wcel
    #
    cY
    cA
    wcel
    #
    wa
    #
    wa
    #
    cX
    cY
    cicc
    co
    #
    cA
    cdif
    #
    c0
    wceq
    @8
    cA
    wss
    @7
    vz
    @9
    @7
    vz
    cv
    #
    @9
    wcel
    #
    @2
    @0
    @2
    @6
    simplr
    @7
    @11
    @2
    wn
    @7
    @11
    wa
    #
    cA
    cmnf
    @10
    cioo
    co
    #
    @1
    @10
    cpnf
    cioo
    co
    #
    cr
    @1
    cr
    ctopon
    cfv
    wcel
    @12
    retopon
    a1i
    @0
    @2
    @6
    @11
    simplll
    #
    @13
    @1
    wcel
    @12
    cmnf
    @10
    iooretop
    a1i
    @14
    @1
    wcel
    @12
    @10
    cpnf
    iooretop
    a1i
    @12
    cX
    @13
    wcel
    #
    @4
    @13
    cA
    cin
    c0
    wne
    @12
    @16
    cX
    cr
    wcel
    #
    cmnf
    cX
    clt
    wbr
    #
    cX
    @10
    clt
    wbr
    #
    @12
    cA
    cr
    cX
    @15
    @3
    @4
    @5
    @11
    simplrl
    #
    sseldd
    #
    @12
    @17
    @18
    @21
    cX
    mnflt
    syl
    @12
    @19
    cX
    @10
    wceq
    #
    @12
    @22
    @10
    cA
    wcel
    #
    @11
    @23
    wn
    #
    @7
    @10
    @8
    cA
    eldifn
    adantl
    #
    @12
    @4
    @22
    @23
    @20
    cX
    @10
    cA
    eleq1
    syl5ibcom
    mtod
    @12
    @19
    @22
    @12
    cX
    @10
    cle
    wbr
    #
    @19
    @22
    wo
    @12
    @10
    cr
    wcel
    #
    @26
    @10
    cY
    cle
    wbr
    #
    @12
    @10
    @8
    wcel
    #
    @27
    @26
    @28
    w3a
    #
    @11
    @29
    @7
    @10
    @8
    cA
    eldifi
    adantl
    @12
    @17
    cY
    cr
    wcel
    #
    @29
    @30
    wb
    @21
    @12
    cA
    cr
    cY
    @15
    @3
    @4
    @5
    @11
    simplrr
    #
    sseldd
    #
    cX
    cY
    @10
    elicc2
    syl2anc
    mpbid
    #
    simp2d
    @12
    cX
    @10
    @21
    @12
    @27
    @26
    @28
    @34
    simp1d
    #
    leloed
    mpbid
    ord
    mt3d
    @12
    cmnf
    cxr
    wcel
    #
    @10
    cxr
    wcel
    #
    @16
    @17
    @18
    @19
    w3a
    wb
    mnfxr
    @12
    @10
    @35
    rexrd
    #
    cmnf
    @10
    cX
    elioo2
    sylancr
    mpbir3and
    @20
    cX
    @13
    cA
    inelcm
    syl2anc
    @12
    cY
    @14
    wcel
    #
    @5
    @14
    cA
    cin
    c0
    wne
    @12
    @39
    @31
    @10
    cY
    clt
    wbr
    #
    cY
    cpnf
    clt
    wbr
    #
    @33
    @12
    @40
    @10
    cY
    wceq
    #
    @12
    @42
    @23
    @25
    @12
    @23
    @42
    @5
    @32
    @10
    cY
    cA
    eleq1
    syl5ibrcom
    mtod
    @12
    @40
    @42
    @12
    @28
    @40
    @42
    wo
    @12
    @27
    @26
    @28
    @34
    simp3d
    @12
    @10
    cY
    @35
    @33
    leloed
    mpbid
    ord
    mt3d
    @12
    @31
    @41
    @33
    cY
    ltpnf
    syl
    @12
    @37
    cpnf
    cxr
    wcel
    #
    @39
    @31
    @40
    @41
    w3a
    wb
    @38
    pnfxr
    @10
    cpnf
    cY
    elioo2
    sylancl
    mpbir3and
    @32
    cY
    @14
    cA
    inelcm
    syl2anc
    @12
    @13
    @14
    cin
    #
    cA
    cin
    #
    @44
    wss
    @44
    c0
    wceq
    #
    @45
    c0
    wceq
    @44
    cA
    inss1
    @12
    @36
    @37
    wa
    @37
    @43
    wa
    @10
    @10
    cle
    wbr
    @46
    @12
    @37
    @36
    @38
    mnfxr
    jctil
    @12
    @37
    @43
    @38
    pnfxr
    jctir
    @12
    @10
    @35
    leidd
    cmnf
    @10
    @10
    cpnf
    ioodisj
    syl21anc
    @45
    @44
    sseq0
    sylancr
    @12
    cA
    @10
    csn
    #
    @13
    @14
    cun
    #
    cun
    #
    wss
    #
    cA
    @48
    wss
    #
    @12
    cA
    cr
    @49
    @15
    @12
    @13
    @47
    cun
    @14
    cun
    #
    cmnf
    cpnf
    cioo
    co
    #
    @49
    cr
    @12
    @36
    @37
    @43
    cmnf
    @10
    clt
    wbr
    #
    @10
    cpnf
    clt
    wbr
    #
    @52
    @53
    wceq
    @36
    @12
    mnfxr
    a1i
    @38
    @43
    @12
    pnfxr
    a1i
    @12
    @27
    @54
    @35
    @10
    mnflt
    syl
    @12
    @27
    @55
    @35
    @10
    ltpnf
    syl
    cmnf
    @10
    cpnf
    ioojoin
    syl32anc
    @52
    @13
    @47
    @14
    cun
    cun
    @49
    @13
    @47
    @14
    unass
    @13
    @47
    @14
    un12
    eqtri
    ioomax
    3eqtr3g
    sseqtr4d
    @12
    cA
    @47
    cin
    c0
    wceq
    #
    @50
    @51
    wb
    @12
    @24
    @56
    @25
    cA
    @10
    disjsn
    sylibr
    cA
    @47
    @48
    disjssun
    syl
    mpbid
    nconnsubb
    ex
    mt2d
    eq0rdv
    @8
    cA
    ssdif0
    sylibr
end
