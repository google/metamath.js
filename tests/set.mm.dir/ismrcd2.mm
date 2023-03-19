include "cpw.mm"
include "cid.mm"
include "cin.mm"
include "cdm.mm"
include "cmrc.mm"
include "cfv.mm"
include "wf.mm"
include "wfn.mm"
include "ffn.mm"
include "syl.mm"
include "cmre.mm"
include "wcel.mm"
include "ismrcd1.mm"
include "eqid.mm"
include "mrcf.mm"
include "3syl.mm"
include "cv.mm"
include "wa.mm"
include "wss.mm"
include "mrcssvd.mm"
include "adantr.mm"
include "elpwi.mm"
include "mrcssid.mm"
include "syl2an.mm"
include "wi.mm"
include "wal.mm"
include "3expib.mm"
include "alrimivv.mm"
include "cvv.mm"
include "vex.mm"
include "fvex.mm"
include "weq.mm"
include "wceq.mm"
include "wb.mm"
include "sseq1.mm"
include "adantl.mm"
include "sseq12.mm"
include "anbi12d.mm"
include "fveq2.mm"
include "imbi12d.mm"
include "spc2gv.mm"
include "mp2an.mm"
include "mp2and.mm"
include "mrccl.mm"
include "elpw.mm"
include "sylibr.mm"
include "fnelfp.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "sseqtrd.mm"
include "anbi2d.mm"
include "id.mm"
include "sseq12d.mm"
include "chvarv.mm"
include "sylan2.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "ffvelrnda.mm"
include "mpbird.mm"
include "mrcsscl.mm"
include "syl3anc.mm"
include "eqssd.mm"
include "eqfnfvd.mm"

theorem ismrcd2
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
  assert |- ( ph -> F = ( mrCls ` dom ( F i^i _I ) ) )

  proof
    wph
    vz
    cB
    cpw
    #
    cF
    cF
    cid
    cin
    cdm
    #
    cmrc
    cfv
    #
    wph
    @0
    @0
    cF
    wf
    cF
    @0
    wfn
    #
    ismrcd.f
    @0
    @0
    cF
    ffn
    syl
    #
    wph
    @1
    cB
    cmre
    cfv
    wcel
    #
    @0
    @1
    @2
    wf
    @2
    @0
    wfn
    wph
    vx
    vy
    cB
    cF
    cV
    ismrcd.b
    ismrcd.f
    ismrcd.e
    ismrcd.m
    ismrcd.i
    ismrcd1
    #
    @1
    @2
    cB
    @2
    eqid
    #
    mrcf
    @0
    @1
    @2
    ffn
    3syl
    wph
    vz
    cv
    #
    @0
    wcel
    #
    wa
    #
    @8
    cF
    cfv
    #
    @8
    @2
    cfv
    #
    @10
    @11
    @12
    cF
    cfv
    #
    @12
    @10
    @12
    cB
    wss
    #
    @8
    @12
    wss
    #
    @11
    @13
    wss
    #
    wph
    @14
    @9
    wph
    @1
    @8
    @2
    cB
    @6
    @7
    mrcssvd
    #
    adantr
    wph
    @5
    @8
    cB
    wss
    #
    @15
    @9
    @6
    @8
    cB
    elpwi
    #
    @1
    @8
    @2
    cB
    @7
    mrcssid
    syl2an
    wph
    @14
    @15
    wa
    #
    @16
    wi
    #
    @9
    wph
    vx
    cv
    #
    cB
    wss
    #
    vy
    cv
    #
    @22
    wss
    #
    wa
    #
    @24
    cF
    cfv
    #
    @22
    cF
    cfv
    #
    wss
    #
    wi
    #
    vx
    wal
    vy
    wal
    #
    @21
    wph
    @30
    vy
    vx
    wph
    @23
    @25
    @29
    ismrcd.m
    3expib
    alrimivv
    @8
    cvv
    wcel
    @12
    cvv
    wcel
    @31
    @21
    wi
    vz
    vex
    @8
    @2
    fvex
    #
    @30
    @21
    vy
    vx
    @8
    @12
    cvv
    cvv
    vy
    vz
    weq
    #
    @22
    @12
    wceq
    #
    wa
    #
    @26
    @20
    @29
    @16
    @35
    @23
    @14
    @25
    @15
    @34
    @23
    @14
    wb
    @33
    @22
    @12
    cB
    sseq1
    adantl
    @24
    @8
    @22
    @12
    sseq12
    anbi12d
    @33
    @27
    @11
    wceq
    @28
    @13
    wceq
    @29
    @16
    wb
    @34
    @24
    @8
    cF
    fveq2
    @22
    @12
    cF
    fveq2
    @27
    @11
    @28
    @13
    sseq12
    syl2an
    imbi12d
    spc2gv
    mp2an
    syl
    adantr
    mp2and
    @10
    @12
    @1
    wcel
    #
    @13
    @12
    wceq
    #
    wph
    @5
    @18
    @36
    @9
    @6
    @19
    @1
    @8
    @2
    cB
    @7
    mrccl
    syl2an
    @10
    @3
    @12
    @0
    wcel
    #
    @36
    @37
    wb
    wph
    @3
    @9
    @4
    adantr
    #
    wph
    @38
    @9
    wph
    @14
    @38
    @17
    @12
    cB
    @32
    elpw
    sylibr
    adantr
    @0
    cF
    @12
    fnelfp
    syl2anc
    mpbid
    sseqtrd
    @10
    @5
    @8
    @11
    wss
    #
    @11
    @1
    wcel
    #
    @12
    @11
    wss
    wph
    @5
    @9
    @6
    adantr
    @9
    wph
    @18
    @40
    @19
    wph
    @23
    wa
    #
    @22
    @28
    wss
    #
    wi
    wph
    @18
    wa
    #
    @40
    wi
    vx
    vz
    vx
    vz
    weq
    #
    @42
    @44
    @43
    @40
    @45
    @23
    @18
    wph
    @22
    @8
    cB
    sseq1
    anbi2d
    #
    @45
    @22
    @8
    @28
    @11
    @45
    id
    @22
    @8
    cF
    fveq2
    #
    sseq12d
    imbi12d
    ismrcd.e
    chvarv
    sylan2
    @10
    @41
    @11
    cF
    cfv
    #
    @11
    wceq
    #
    @9
    wph
    @18
    @49
    @19
    @42
    @28
    cF
    cfv
    #
    @28
    wceq
    #
    wi
    @44
    @49
    wi
    vx
    vz
    @45
    @42
    @44
    @51
    @49
    @46
    @45
    @50
    @48
    @28
    @11
    @45
    @28
    @11
    cF
    @47
    fveq2d
    @47
    eqeq12d
    imbi12d
    ismrcd.i
    chvarv
    sylan2
    @10
    @3
    @11
    @0
    wcel
    @41
    @49
    wb
    @39
    wph
    @0
    @0
    @8
    cF
    ismrcd.f
    ffvelrnda
    @0
    cF
    @11
    fnelfp
    syl2anc
    mpbird
    @1
    @8
    @2
    @11
    cB
    @7
    mrcsscl
    syl3anc
    eqssd
    eqfnfvd
end
