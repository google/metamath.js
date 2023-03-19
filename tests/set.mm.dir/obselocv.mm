include "cobs.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "wn.mm"
include "wa.mm"
include "wi.mm"
include "c0g.mm"
include "wne.mm"
include "eqid.mm"
include "obsne0.mm"
include "3adant2.mm"
include "csn.mm"
include "wceq.mm"
include "cin.mm"
include "elin.mm"
include "clspn.mm"
include "clmod.mm"
include "cbs.mm"
include "cphl.mm"
include "obsrcl.mm"
include "3ad2ant1.mm"
include "phllmod.mm"
include "syl.mm"
include "simp2.mm"
include "obsss.mm"
include "sstrd.mm"
include "lspssid.mm"
include "syl2anc.mm"
include "ssrin.mm"
include "ocvlsp.mm"
include "ineq2d.mm"
include "clss.mm"
include "lspcl.mm"
include "ocvin.mm"
include "eqtr3d.mm"
include "sseqtrd.mm"
include "sseld.mm"
include "syl5bir.mm"
include "elsni.mm"
include "syl6.mm"
include "necon3ad.mm"
include "mpd.mm"
include "imnan.mm"
include "sylibr.mm"
include "con2d.mm"
include "cv.mm"
include "cip.mm"
include "co.mm"
include "csca.mm"
include "wral.mm"
include "simpr.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "con3d.mm"
include "cur.mm"
include "cif.mm"
include "simpl1.mm"
include "simpl3.mm"
include "sselda.mm"
include "obsip.mm"
include "syl3anc.mm"
include "iffalse.mm"
include "eqeq2d.mm"
include "syl5ibcom.mm"
include "syld.mm"
include "ralrimdva.mm"
include "wb.mm"
include "simp3.mm"
include "sseldd.mm"
include "elocv.mm"
include "df-3an.mm"
include "bitri.mm"
include "baib.mm"
include "sylibrd.mm"
include "impbid.mm"

theorem obselocv
  let cA: class A
  let cB: class B
  let cC: class C
  let c.pe: class ._|_
  let cW: class W
  let vx: setvar x
  assume obselocv.o: |- ._|_ = ( ocv ` W )


  assert |- ( ( B e. ( OBasis ` W ) /\ C C_ B /\ A e. B ) -> ( A e. ( ._|_ ` C ) <-> -. A e. C ) )

  proof
    cB
    cW
    cobs
    cfv
    wcel
    #
    cC
    cB
    wss
    #
    cA
    cB
    wcel
    #
    w3a
    #
    cA
    cC
    c.pe
    cfv
    #
    wcel
    #
    cA
    cC
    wcel
    #
    wn
    #
    @3
    @6
    @5
    @3
    @6
    @5
    wa
    #
    wn
    #
    @6
    @5
    wn
    wi
    @3
    cA
    cW
    c0g
    cfv
    #
    wne
    #
    @9
    @0
    @2
    @11
    @1
    cA
    cB
    cW
    @10
    @10
    eqid
    #
    obsne0
    3adant2
    @3
    @8
    cA
    @10
    @3
    @8
    cA
    @10
    csn
    #
    wcel
    #
    cA
    @10
    wceq
    @8
    cA
    cC
    @4
    cin
    #
    wcel
    @3
    @14
    cA
    cC
    @4
    elin
    @3
    @15
    @13
    cA
    @3
    @15
    cC
    cW
    clspn
    cfv
    #
    cfv
    #
    @4
    cin
    #
    @13
    @3
    cC
    @17
    wss
    #
    @15
    @18
    wss
    @3
    cW
    clmod
    wcel
    #
    cC
    cW
    cbs
    cfv
    #
    wss
    #
    @19
    @3
    cW
    cphl
    wcel
    #
    @20
    @0
    @1
    @23
    @2
    cB
    cW
    obsrcl
    3ad2ant1
    #
    cW
    phllmod
    syl
    #
    @3
    cC
    cB
    @21
    @0
    @1
    @2
    simp2
    #
    @0
    @1
    cB
    @21
    wss
    @2
    cB
    @21
    cW
    @21
    eqid
    #
    obsss
    3ad2ant1
    #
    sstrd
    #
    cC
    @16
    @21
    cW
    @27
    @16
    eqid
    #
    lspssid
    syl2anc
    cC
    @17
    @4
    ssrin
    syl
    @3
    @17
    @17
    c.pe
    cfv
    #
    cin
    #
    @18
    @13
    @3
    @31
    @4
    @17
    @3
    @23
    @22
    @31
    @4
    wceq
    @24
    @29
    cC
    @16
    c.pe
    @21
    cW
    @27
    obselocv.o
    @30
    ocvlsp
    syl2anc
    ineq2d
    @3
    @23
    @17
    cW
    clss
    cfv
    #
    wcel
    #
    @32
    @13
    wceq
    @24
    @3
    @20
    @22
    @34
    @25
    @29
    @33
    cC
    @16
    @21
    cW
    @27
    @33
    eqid
    #
    @30
    lspcl
    syl2anc
    @17
    @33
    c.pe
    cW
    @10
    obselocv.o
    @35
    @12
    ocvin
    syl2anc
    eqtr3d
    sseqtrd
    sseld
    syl5bir
    cA
    @10
    elsni
    syl6
    necon3ad
    mpd
    @6
    @5
    imnan
    sylibr
    con2d
    @3
    @7
    cA
    vx
    cv
    #
    cW
    cip
    cfv
    #
    co
    #
    cW
    csca
    cfv
    #
    c0g
    cfv
    #
    wceq
    #
    vx
    cC
    wral
    #
    @5
    @3
    @7
    @41
    vx
    cC
    @3
    @36
    cC
    wcel
    #
    wa
    #
    @7
    cA
    @36
    wceq
    #
    wn
    #
    @41
    @44
    @45
    @6
    @44
    @6
    @45
    @43
    @3
    @43
    simpr
    cA
    @36
    cC
    eleq1
    syl5ibrcom
    con3d
    @44
    @38
    @45
    @39
    cur
    cfv
    #
    @40
    cif
    #
    wceq
    #
    @46
    @41
    @44
    @0
    @2
    @36
    cB
    wcel
    @49
    @0
    @1
    @2
    @43
    simpl1
    @0
    @1
    @2
    @43
    simpl3
    @3
    cC
    cB
    @36
    @26
    sselda
    cB
    cA
    @36
    @47
    @39
    @37
    @21
    cW
    @40
    @27
    @37
    eqid
    #
    @39
    eqid
    #
    @47
    eqid
    @40
    eqid
    #
    obsip
    syl3anc
    @46
    @48
    @40
    @38
    @45
    @47
    @40
    iffalse
    eqeq2d
    syl5ibcom
    syld
    ralrimdva
    @3
    @22
    cA
    @21
    wcel
    #
    @5
    @42
    wb
    @29
    @3
    cB
    @21
    cA
    @28
    @0
    @1
    @2
    simp3
    sseldd
    @5
    @22
    @53
    wa
    #
    @42
    @5
    @22
    @53
    @42
    w3a
    @54
    @42
    wa
    vx
    cA
    cC
    @39
    @37
    c.pe
    @21
    cW
    @40
    @27
    @50
    @51
    @52
    obselocv.o
    elocv
    @22
    @53
    @42
    df-3an
    bitri
    baib
    syl2anc
    sylibrd
    impbid
end
