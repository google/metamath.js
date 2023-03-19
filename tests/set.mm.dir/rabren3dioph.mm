include "cn0.mm"
include "wcel.mm"
include "c1.mm"
include "c3.mm"
include "cfz.mm"
include "co.mm"
include "cmap.mm"
include "crab.mm"
include "cdioph.mm"
include "cfv.mm"
include "wa.mm"
include "cv.mm"
include "cop.mm"
include "c2.mm"
include "ctp.mm"
include "ccom.mm"
include "wsbc.mm"
include "vex.mm"
include "tpex.mm"
include "coex.mm"
include "wceq.mm"
include "w3a.mm"
include "wb.mm"
include "wfn.mm"
include "wne.mm"
include "1ne2.mm"
include "1re.mm"
include "1lt3.mm"
include "ltneii.mm"
include "2re.mm"
include "2lt3.mm"
include "1ex.mm"
include "2ex.mm"
include "3ex.mm"
include "elexi.mm"
include "fntp.mm"
include "mp3an.mm"
include "tpid1.mm"
include "fvco2.mm"
include "mp2an.mm"
include "fvtp1.mm"
include "fveq2i.mm"
include "eqtri.mm"
include "tpid2.mm"
include "fvtp2.mm"
include "tpid3.mm"
include "fvtp3.mm"
include "3pm3.2i.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "3anbi123d.mm"
include "mpbiri.mm"
include "syl.mm"
include "sbcie.mm"
include "rabbii.mm"
include "wf.mm"
include "wss.mm"
include "ftp.mm"
include "caddc.mm"
include "cz.mm"
include "1z.mm"
include "fztp.mm"
include "ax-mp.mm"
include "1p2e3.mm"
include "oveq2i.mm"
include "eqidd.mm"
include "1p1e2.mm"
include "a1i.mm"
include "tpeq123d.mm"
include "3eqtr3i.mm"
include "feq2i.mm"
include "mpbir.mm"
include "tpss.mm"
include "mpbi.mm"
include "fss.mm"
include "rabrenfdioph.mm"
include "mp3an2.mm"
include "syl5eqelr.mm"

theorem rabren3dioph
  let wph: wff ph
  let wps: wff ps
  let cN: class N
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  assume rabren3dioph.a: |- ( ( ( a ` 1 ) = ( b ` X ) /\ ( a ` 2 ) = ( b ` Y ) /\ ( a ` 3 ) = ( b ` Z ) ) -> ( ph <-> ps ) )
  assume rabren3dioph.b: |- X e. ( 1 ... N )
  assume rabren3dioph.c: |- Y e. ( 1 ... N )
  assume rabren3dioph.d: |- Z e. ( 1 ... N )

  disjoint a ps
  disjoint b ph
  disjoint X a
  disjoint X b
  disjoint a b
  disjoint Y a
  disjoint Y b
  disjoint Z a
  disjoint Z b
  disjoint N a
  disjoint N b
  assert |- ( ( N e. NN0 /\ { a e. ( NN0 ^m ( 1 ... 3 ) ) | ph } e. ( Dioph ` 3 ) ) -> { b e. ( NN0 ^m ( 1 ... N ) ) | ps } e. ( Dioph ` N ) )

  proof
    cN
    cn0
    wcel
    #
    wph
    va
    cn0
    c1
    c3
    cfz
    co
    #
    cmap
    co
    crab
    c3
    cdioph
    cfv
    wcel
    #
    wa
    wps
    vb
    cn0
    c1
    cN
    cfz
    co
    #
    cmap
    co
    #
    crab
    wph
    va
    vb
    cv
    #
    c1
    cX
    cop
    #
    c2
    cY
    cop
    #
    c3
    cZ
    cop
    #
    ctp
    #
    ccom
    #
    wsbc
    #
    vb
    @4
    crab
    #
    cN
    cdioph
    cfv
    #
    @11
    wps
    vb
    @4
    wph
    wps
    va
    @10
    @5
    @9
    vb
    vex
    @6
    @7
    @8
    tpex
    coex
    va
    cv
    #
    @10
    wceq
    #
    c1
    @14
    cfv
    #
    cX
    @5
    cfv
    #
    wceq
    #
    c2
    @14
    cfv
    #
    cY
    @5
    cfv
    #
    wceq
    #
    c3
    @14
    cfv
    #
    cZ
    @5
    cfv
    #
    wceq
    #
    w3a
    #
    wph
    wps
    wb
    @15
    @25
    c1
    @10
    cfv
    #
    @17
    wceq
    #
    c2
    @10
    cfv
    #
    @20
    wceq
    #
    c3
    @10
    cfv
    #
    @23
    wceq
    #
    w3a
    @27
    @29
    @31
    @26
    c1
    @9
    cfv
    #
    @5
    cfv
    #
    @17
    @9
    c1
    c2
    c3
    ctp
    #
    wfn
    #
    c1
    @34
    wcel
    @26
    @33
    wceq
    c1
    c2
    wne
    #
    c1
    c3
    wne
    #
    c2
    c3
    wne
    #
    @35
    1ne2
    c1
    c3
    1re
    1lt3
    ltneii
    #
    c2
    c3
    2re
    2lt3
    ltneii
    #
    c1
    c2
    c3
    cX
    cY
    cZ
    1ex
    2ex
    3ex
    cX
    @3
    rabren3dioph.b
    elexi
    #
    cY
    @3
    rabren3dioph.c
    elexi
    #
    cZ
    @3
    rabren3dioph.d
    elexi
    #
    fntp
    mp3an
    #
    c1
    c2
    c3
    1ex
    tpid1
    @34
    @5
    @9
    c1
    fvco2
    mp2an
    @32
    cX
    @5
    @36
    @37
    @32
    cX
    wceq
    1ne2
    @39
    c1
    c2
    c3
    cX
    cY
    cZ
    1ex
    @41
    fvtp1
    mp2an
    fveq2i
    eqtri
    @28
    c2
    @9
    cfv
    #
    @5
    cfv
    #
    @20
    @35
    c2
    @34
    wcel
    @28
    @46
    wceq
    @44
    c1
    c2
    c3
    2ex
    tpid2
    @34
    @5
    @9
    c2
    fvco2
    mp2an
    @45
    cY
    @5
    @36
    @38
    @45
    cY
    wceq
    1ne2
    @40
    c1
    c2
    c3
    cX
    cY
    cZ
    2ex
    @42
    fvtp2
    mp2an
    fveq2i
    eqtri
    @30
    c3
    @9
    cfv
    #
    @5
    cfv
    #
    @23
    @35
    c3
    @34
    wcel
    @30
    @48
    wceq
    @44
    c1
    c2
    c3
    3ex
    tpid3
    @34
    @5
    @9
    c3
    fvco2
    mp2an
    @47
    cZ
    @5
    @37
    @38
    @47
    cZ
    wceq
    @39
    @40
    c1
    c2
    c3
    cX
    cY
    cZ
    3ex
    @43
    fvtp3
    mp2an
    fveq2i
    eqtri
    3pm3.2i
    @15
    @18
    @27
    @21
    @29
    @24
    @31
    @15
    @16
    @26
    @17
    c1
    @14
    @10
    fveq1
    eqeq1d
    @15
    @19
    @28
    @20
    c2
    @14
    @10
    fveq1
    eqeq1d
    @15
    @22
    @30
    @23
    c3
    @14
    @10
    fveq1
    eqeq1d
    3anbi123d
    mpbiri
    rabren3dioph.a
    syl
    sbcie
    rabbii
    @0
    @1
    @3
    @9
    wf
    #
    @2
    @12
    @13
    wcel
    @1
    cX
    cY
    cZ
    ctp
    #
    @9
    wf
    #
    @50
    @3
    wss
    #
    @49
    @51
    @34
    @50
    @9
    wf
    c1
    c2
    c3
    cX
    cY
    cZ
    1ex
    2ex
    3ex
    @41
    @42
    @43
    1ne2
    @39
    @40
    ftp
    @1
    @34
    @50
    @9
    c1
    c1
    c2
    caddc
    co
    #
    cfz
    co
    #
    c1
    c1
    c1
    caddc
    co
    #
    @53
    ctp
    #
    @1
    @34
    c1
    cz
    wcel
    #
    @54
    @56
    wceq
    1z
    c1
    fztp
    ax-mp
    @53
    c3
    c1
    cfz
    1p2e3
    oveq2i
    @57
    @56
    @34
    wceq
    1z
    @57
    c1
    c1
    @55
    c2
    @53
    c3
    @57
    c1
    eqidd
    @55
    c2
    wceq
    @57
    1p1e2
    a1i
    @53
    c3
    wceq
    @57
    1p2e3
    a1i
    tpeq123d
    ax-mp
    3eqtr3i
    feq2i
    mpbir
    cX
    @3
    wcel
    #
    cY
    @3
    wcel
    #
    cZ
    @3
    wcel
    #
    w3a
    @52
    @58
    @59
    @60
    rabren3dioph.b
    rabren3dioph.c
    rabren3dioph.d
    3pm3.2i
    cX
    cY
    cZ
    @3
    @41
    @42
    @43
    tpss
    mpbi
    @1
    @50
    @3
    @9
    fss
    mp2an
    wph
    c3
    cN
    @9
    va
    vb
    rabrenfdioph
    mp3an2
    syl5eqelr
end
