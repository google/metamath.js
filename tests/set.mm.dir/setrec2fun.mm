include "cv.mm"
include "wss.mm"
include "cfv.mm"
include "wi.mm"
include "wal.mm"
include "cab.mm"
include "cuni.mm"
include "csetrecs.mm"
include "df-setrecs.mm"
include "eqtri.mm"
include "wral.mm"
include "wcel.mm"
include "cvv.mm"
include "eqid.mm"
include "vex.mm"
include "a1i.mm"
include "setrec1lem1.mm"
include "wa.mm"
include "cpw.mm"
include "cima.mm"
include "cin.mm"
include "w3a.mm"
include "id.mm"
include "inss1.mm"
include "syl6ss.mm"
include "nfv.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfss.mm"
include "nfim.mm"
include "weq.mm"
include "sseq1.mm"
include "fveq2.mm"
include "sseq1d.mm"
include "imbi12d.mm"
include "biimpd.mm"
include "spim.mm"
include "syl.mm"
include "syl5.mm"
include "imp.mm"
include "3adant2.mm"
include "c0.mm"
include "wceq.mm"
include "wn.mm"
include "selpw.mm"
include "eliman0.mm"
include "ex.mm"
include "sylbir.mm"
include "elssuni.mm"
include "syl6.mm"
include "0ss.mm"
include "syl6eqss.mm"
include "pm2.61d2.mm"
include "3ad2ant2.mm"
include "ssind.mm"
include "3exp.mm"
include "alrimiv.mm"
include "wfun.mm"
include "pwex.mm"
include "funimaex.mm"
include "ax-mp.mm"
include "uniex.mm"
include "inex2.mm"
include "sseq2.mm"
include "imbi2d.mm"
include "albidv.mm"
include "spcv.mm"
include "mpan9.mm"
include "sylbid.mm"
include "ralrimiv.mm"
include "unissb.mm"
include "sylibr.mm"
include "syl5eqss.mm"

theorem setrec2fun
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cF: class F
  let va: setvar a
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vk: setvar k
  assume setrec2fun.1: |- F/_ a F
  assume setrec2fun.2: |- B = setrecs ( F )
  assume setrec2fun.3: |- Fun F
  assume setrec2fun.4: |- ( ph -> A. a ( a C_ C -> ( F ` a ) C_ C ) )

  disjoint C a
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint C w
  disjoint x y
  disjoint x z
  disjoint C x
  disjoint y z
  disjoint C y
  disjoint C z
  disjoint F y
  disjoint F w
  disjoint F x
  disjoint F z
  disjoint a w
  disjoint ph x
  disjoint ph w
  disjoint k x
  assert |- ( ph -> B C_ C )

  proof
    wph
    cB
    vw
    cv
    #
    vy
    cv
    #
    wss
    @0
    vz
    cv
    #
    wss
    #
    @0
    cF
    cfv
    #
    @2
    wss
    #
    wi
    #
    wi
    vw
    wal
    @1
    @2
    wss
    wi
    vz
    wal
    vy
    cab
    #
    cuni
    #
    cC
    cB
    cF
    csetrecs
    @8
    setrec2fun.2
    vy
    vz
    vw
    cF
    df-setrecs
    eqtri
    wph
    vx
    cv
    #
    cC
    wss
    #
    vx
    @7
    wral
    @8
    cC
    wss
    wph
    @10
    vx
    @7
    wph
    @9
    @7
    wcel
    @0
    @9
    wss
    #
    @6
    wi
    #
    vw
    wal
    #
    @9
    @2
    wss
    #
    wi
    #
    vz
    wal
    #
    @10
    wph
    vy
    vz
    vw
    cF
    cvv
    @9
    @7
    @7
    eqid
    @9
    cvv
    wcel
    wph
    vx
    vex
    #
    a1i
    setrec1lem1
    wph
    @16
    @10
    wph
    @16
    wa
    @9
    cC
    cF
    @9
    cpw
    #
    cima
    #
    cuni
    #
    cin
    #
    cC
    wph
    @11
    @0
    @21
    wss
    #
    @4
    @21
    wss
    #
    wi
    #
    wi
    #
    vw
    wal
    #
    @16
    @9
    @21
    wss
    #
    wph
    @25
    vw
    wph
    @11
    @22
    @23
    wph
    @11
    @22
    w3a
    @4
    cC
    @20
    wph
    @22
    @4
    cC
    wss
    #
    @11
    wph
    @22
    @28
    @22
    @0
    cC
    wss
    #
    wph
    @28
    @22
    @0
    @21
    cC
    @22
    id
    cC
    @20
    inss1
    #
    syl6ss
    wph
    va
    cv
    #
    cC
    wss
    #
    @31
    cF
    cfv
    #
    cC
    wss
    #
    wi
    #
    va
    wal
    @29
    @28
    wi
    #
    setrec2fun.4
    @35
    @36
    va
    vw
    @29
    @28
    va
    @29
    va
    nfv
    va
    @4
    cC
    va
    @0
    cF
    setrec2fun.1
    va
    @0
    nfcv
    nffv
    va
    cC
    nfcv
    nfss
    nfim
    va
    vw
    weq
    #
    @35
    @36
    @37
    @32
    @29
    @34
    @28
    @31
    @0
    cC
    sseq1
    @37
    @33
    @4
    cC
    @31
    @0
    cF
    fveq2
    sseq1d
    imbi12d
    biimpd
    spim
    syl
    syl5
    imp
    3adant2
    @11
    wph
    @4
    @20
    wss
    #
    @22
    @11
    @4
    c0
    wceq
    #
    @38
    @11
    @39
    wn
    #
    @4
    @19
    wcel
    #
    @38
    @11
    @0
    @18
    wcel
    #
    @40
    @41
    wi
    vw
    @9
    selpw
    @42
    @40
    @41
    @0
    @18
    cF
    eliman0
    ex
    sylbir
    @4
    @19
    elssuni
    syl6
    @39
    @4
    c0
    @20
    @39
    id
    @20
    0ss
    syl6eqss
    pm2.61d2
    3ad2ant2
    ssind
    3exp
    alrimiv
    @15
    @26
    @27
    wi
    vz
    @21
    @20
    cC
    @19
    cF
    wfun
    @19
    cvv
    wcel
    setrec2fun.3
    cF
    @18
    @9
    @17
    pwex
    funimaex
    ax-mp
    uniex
    inex2
    @2
    @21
    wceq
    #
    @13
    @26
    @14
    @27
    @43
    @12
    @25
    vw
    @43
    @6
    @24
    @11
    @43
    @3
    @22
    @5
    @23
    @2
    @21
    @0
    sseq2
    @2
    @21
    @4
    sseq2
    imbi12d
    imbi2d
    albidv
    @2
    @21
    @9
    sseq2
    imbi12d
    spcv
    mpan9
    @30
    syl6ss
    ex
    sylbid
    ralrimiv
    vx
    @7
    cC
    unissb
    sylibr
    syl5eqss
end
