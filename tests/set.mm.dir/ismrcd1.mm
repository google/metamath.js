include "cid.mm"
include "cin.mm"
include "cdm.mm"
include "cpw.mm"
include "wss.mm"
include "inss1.mm"
include "dmss.mm"
include "ax-mp.mm"
include "wf.mm"
include "wceq.mm"
include "fdm.mm"
include "syl.mm"
include "syl5sseq.mm"
include "wcel.mm"
include "cfv.mm"
include "ssid.mm"
include "wb.mm"
include "elpwg.mm"
include "mpbiri.mm"
include "ffvelrnd.mm"
include "elpwid.mm"
include "cv.mm"
include "wral.mm"
include "selpw.mm"
include "sylan2b.mm"
include "ralrimiva.mm"
include "id.mm"
include "fveq2.mm"
include "sseq12d.mm"
include "rspcva.mm"
include "syl2anc.mm"
include "eqssd.mm"
include "wfn.mm"
include "ffn.mm"
include "fnelfp.mm"
include "mpbird.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "cint.mm"
include "wel.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "cuni.mm"
include "simp2.mm"
include "3ad2ant1.mm"
include "sstrd.mm"
include "simp3.mm"
include "intssuni2.mm"
include "unipw.mm"
include "syl6sseq.mm"
include "cvv.mm"
include "intex.mm"
include "sylbi.mm"
include "3ad2ant3.mm"
include "adantr.mm"
include "3expib.mm"
include "alrimiv.mm"
include "sselda.mm"
include "intss1.mm"
include "adantl.mm"
include "jca.mm"
include "sseq1.mm"
include "anbi2d.mm"
include "sseq1d.mm"
include "imbi12d.mm"
include "spcgv.mm"
include "syl3c.mm"
include "mpbid.mm"
include "sseqtrd.mm"
include "ssint.mm"
include "sylibr.mm"
include "ismred.mm"

theorem ismrcd1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cF: class F
  let cV: class V
  let vz: setvar z
  assume ismrcd.b: |- ( ph -> B e. V )
  assume ismrcd.f: |- ( ph -> F : ~P B --> ~P B )
  assume ismrcd.e: |- ( ( ph /\ x C_ B ) -> x C_ ( F ` x ) )
  assume ismrcd.m: |- ( ( ph /\ x C_ B /\ y C_ x ) -> ( F ` y ) C_ ( F ` x ) )
  assume ismrcd.i: |- ( ( ph /\ x C_ B ) -> ( F ` ( F ` x ) ) = ( F ` x ) )

  disjoint ph x
  disjoint ph y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint F x
  disjoint F y
  disjoint V x
  disjoint V y
  disjoint ph z
  disjoint x z
  disjoint y z
  disjoint B z
  disjoint F z
  disjoint V z
  assert |- ( ph -> dom ( F i^i _I ) e. ( Moore ` B ) )

  proof
    wph
    cF
    cid
    cin
    #
    cdm
    #
    cB
    vz
    wph
    cF
    cdm
    #
    @1
    cB
    cpw
    #
    @0
    cF
    wss
    @1
    @2
    wss
    cF
    cid
    inss1
    @0
    cF
    dmss
    ax-mp
    wph
    @3
    @3
    cF
    wf
    #
    @2
    @3
    wceq
    ismrcd.f
    @3
    @3
    cF
    fdm
    syl
    syl5sseq
    #
    wph
    cB
    @1
    wcel
    #
    cB
    cF
    cfv
    #
    cB
    wceq
    #
    wph
    @7
    cB
    wph
    @7
    cB
    wph
    @3
    @3
    cB
    cF
    ismrcd.f
    wph
    cB
    @3
    wcel
    #
    cB
    cB
    wss
    #
    cB
    ssid
    wph
    cB
    cV
    wcel
    @9
    @10
    wb
    ismrcd.b
    cB
    cB
    cV
    elpwg
    syl
    mpbiri
    #
    ffvelrnd
    elpwid
    wph
    @9
    vx
    cv
    #
    @12
    cF
    cfv
    #
    wss
    #
    vx
    @3
    wral
    #
    cB
    @7
    wss
    #
    @11
    wph
    @14
    vx
    @3
    @12
    @3
    wcel
    #
    wph
    @12
    cB
    wss
    #
    @14
    vx
    cB
    selpw
    ismrcd.e
    sylan2b
    ralrimiva
    #
    @14
    @16
    vx
    cB
    @3
    @12
    cB
    wceq
    #
    @12
    cB
    @13
    @7
    @20
    id
    @12
    cB
    cF
    fveq2
    sseq12d
    rspcva
    syl2anc
    eqssd
    wph
    cF
    @3
    wfn
    #
    @9
    @6
    @8
    wb
    wph
    @4
    @21
    ismrcd.f
    @3
    @3
    cF
    ffn
    syl
    #
    @11
    @3
    cF
    cB
    fnelfp
    syl2anc
    mpbird
    wph
    vz
    cv
    #
    @1
    wss
    #
    @23
    c0
    wne
    #
    w3a
    #
    @23
    cint
    #
    @1
    wcel
    #
    @27
    cF
    cfv
    #
    @27
    wceq
    #
    @26
    @29
    @27
    @26
    @29
    @12
    wss
    #
    vx
    @23
    wral
    @29
    @27
    wss
    @26
    @31
    vx
    @23
    @26
    vx
    vz
    wel
    #
    wa
    #
    @29
    @13
    @12
    @33
    @27
    @3
    wcel
    #
    @18
    vy
    cv
    #
    @12
    wss
    #
    wa
    #
    @35
    cF
    cfv
    #
    @13
    wss
    #
    wi
    #
    vy
    wal
    #
    @18
    @27
    @12
    wss
    #
    wa
    #
    @29
    @13
    wss
    #
    @26
    @34
    @32
    @26
    @34
    @27
    cB
    wss
    #
    @26
    @27
    @3
    cuni
    #
    cB
    @26
    @23
    @3
    wss
    @25
    @27
    @46
    wss
    @26
    @23
    @1
    @3
    wph
    @24
    @25
    simp2
    #
    wph
    @24
    @1
    @3
    wss
    @25
    @5
    3ad2ant1
    sstrd
    #
    wph
    @24
    @25
    simp3
    @23
    @3
    intssuni2
    syl2anc
    cB
    unipw
    syl6sseq
    @25
    wph
    @34
    @45
    wb
    #
    @24
    @25
    @27
    cvv
    wcel
    @49
    @23
    intex
    @27
    cB
    cvv
    elpwg
    sylbi
    3ad2ant3
    mpbird
    #
    adantr
    @26
    @41
    @32
    wph
    @24
    @41
    @25
    wph
    @40
    vy
    wph
    @18
    @36
    @39
    ismrcd.m
    3expib
    alrimiv
    3ad2ant1
    adantr
    @33
    @18
    @42
    @33
    @12
    cB
    @26
    @23
    @3
    @12
    @48
    sselda
    #
    elpwid
    @32
    @42
    @26
    @12
    @23
    intss1
    adantl
    jca
    @40
    @43
    @44
    wi
    vy
    @27
    @3
    @35
    @27
    wceq
    #
    @37
    @43
    @39
    @44
    @52
    @36
    @42
    @18
    @35
    @27
    @12
    sseq1
    anbi2d
    @52
    @38
    @29
    @13
    @35
    @27
    cF
    fveq2
    sseq1d
    imbi12d
    spcgv
    syl3c
    @33
    @12
    @1
    wcel
    #
    @13
    @12
    wceq
    #
    @26
    @23
    @1
    @12
    @47
    sselda
    @33
    @21
    @17
    @53
    @54
    wb
    @26
    @21
    @32
    wph
    @24
    @21
    @25
    @22
    3ad2ant1
    #
    adantr
    @51
    @3
    cF
    @12
    fnelfp
    syl2anc
    mpbid
    sseqtrd
    ralrimiva
    vx
    @29
    @23
    ssint
    sylibr
    @26
    @34
    @15
    @27
    @29
    wss
    #
    @50
    wph
    @24
    @15
    @25
    @19
    3ad2ant1
    @14
    @56
    vx
    @27
    @3
    @12
    @27
    wceq
    #
    @12
    @27
    @13
    @29
    @57
    id
    @12
    @27
    cF
    fveq2
    sseq12d
    rspcva
    syl2anc
    eqssd
    @26
    @21
    @34
    @28
    @30
    wb
    @55
    @50
    @3
    cF
    @27
    fnelfp
    syl2anc
    mpbird
    ismred
end
