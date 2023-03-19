include "cv.mm"
include "wss.mm"
include "cfv.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "cun.mm"
include "weq.mm"
include "sseq1.mm"
include "fveq2.mm"
include "sseq1d.mm"
include "imbi12d.mm"
include "sseq2.mm"
include "sseq2d.mm"
include "cbvral2v.mm"
include "wcel.mm"
include "wa.mm"
include "ssun1.mm"
include "simprl.mm"
include "elpwi.mm"
include "adantr.mm"
include "adantl.mm"
include "unssd.mm"
include "vex.mm"
include "unex.mm"
include "elpw.mm"
include "sylibr.mm"
include "simpl.mm"
include "wceq.mm"
include "rspc2va.mm"
include "syl21anc.mm"
include "mpi.mm"
include "ssun2.mm"
include "simprr.mm"
include "ralrimivva.mm"
include "ssequn1.mm"
include "uneq1d.mm"
include "uneq1.mm"
include "fveq2d.mm"
include "sseq12d.mm"
include "uneq2d.mm"
include "uneq2.mm"
include "ancoms.mm"
include "unssad.mm"
include "sseqtrd.mm"
include "ex.mm"
include "syl5bi.mm"
include "impbii.mm"
include "bitri.mm"

theorem isotone1
  let cA: class A
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d

  disjoint A a
  disjoint A b
  disjoint a b
  disjoint F a
  disjoint F b
  disjoint A c
  disjoint A d
  disjoint a c
  disjoint a d
  disjoint b c
  disjoint b d
  disjoint c d
  disjoint F c
  disjoint F d
  assert |- ( A. a e. ~P A A. b e. ~P A ( a C_ b -> ( F ` a ) C_ ( F ` b ) ) <-> A. a e. ~P A A. b e. ~P A ( ( F ` a ) u. ( F ` b ) ) C_ ( F ` ( a u. b ) ) )

  proof
    va
    cv
    #
    vb
    cv
    #
    wss
    #
    @0
    cF
    cfv
    #
    @1
    cF
    cfv
    #
    wss
    #
    wi
    #
    vb
    cA
    cpw
    #
    wral
    va
    @7
    wral
    vc
    cv
    #
    vd
    cv
    #
    wss
    #
    @8
    cF
    cfv
    #
    @9
    cF
    cfv
    #
    wss
    #
    wi
    #
    vd
    @7
    wral
    vc
    @7
    wral
    #
    @3
    @4
    cun
    #
    @0
    @1
    cun
    #
    cF
    cfv
    #
    wss
    #
    vb
    @7
    wral
    va
    @7
    wral
    #
    @6
    @14
    @8
    @1
    wss
    #
    @11
    @4
    wss
    #
    wi
    va
    vb
    vc
    vd
    @7
    @7
    va
    vc
    weq
    #
    @2
    @21
    @5
    @22
    @0
    @8
    @1
    sseq1
    @23
    @3
    @11
    @4
    @0
    @8
    cF
    fveq2
    #
    sseq1d
    imbi12d
    vb
    vd
    weq
    #
    @21
    @10
    @22
    @13
    @1
    @9
    @8
    sseq2
    @25
    @4
    @12
    @11
    @1
    @9
    cF
    fveq2
    #
    sseq2d
    imbi12d
    cbvral2v
    @15
    @20
    @15
    @19
    va
    vb
    @7
    @7
    @15
    @0
    @7
    wcel
    #
    @1
    @7
    wcel
    #
    wa
    #
    wa
    #
    @3
    @4
    @18
    @30
    @0
    @17
    wss
    #
    @3
    @18
    wss
    #
    @0
    @1
    ssun1
    @30
    @27
    @17
    @7
    wcel
    #
    @15
    @31
    @32
    wi
    #
    @15
    @27
    @28
    simprl
    @29
    @33
    @15
    @29
    @17
    cA
    wss
    @33
    @29
    @0
    @1
    cA
    @27
    @0
    cA
    wss
    @28
    @0
    cA
    elpwi
    adantr
    @28
    @1
    cA
    wss
    @27
    @1
    cA
    elpwi
    adantl
    unssd
    @17
    cA
    @0
    @1
    va
    vex
    vb
    vex
    unex
    elpw
    sylibr
    adantl
    #
    @15
    @29
    simpl
    #
    @14
    @34
    @0
    @9
    wss
    #
    @3
    @12
    wss
    #
    wi
    vc
    vd
    @0
    @17
    @7
    @7
    vc
    va
    weq
    #
    @10
    @37
    @13
    @38
    @8
    @0
    @9
    sseq1
    @39
    @11
    @3
    @12
    @8
    @0
    cF
    fveq2
    sseq1d
    imbi12d
    @9
    @17
    wceq
    #
    @37
    @31
    @38
    @32
    @9
    @17
    @0
    sseq2
    @40
    @12
    @18
    @3
    @9
    @17
    cF
    fveq2
    #
    sseq2d
    imbi12d
    rspc2va
    syl21anc
    mpi
    @30
    @1
    @17
    wss
    #
    @4
    @18
    wss
    #
    @1
    @0
    ssun2
    @30
    @28
    @33
    @15
    @42
    @43
    wi
    #
    @15
    @27
    @28
    simprr
    @35
    @36
    @14
    @44
    @1
    @9
    wss
    #
    @4
    @12
    wss
    #
    wi
    vc
    vd
    @1
    @17
    @7
    @7
    vc
    vb
    weq
    #
    @10
    @45
    @13
    @46
    @8
    @1
    @9
    sseq1
    @47
    @11
    @4
    @12
    @8
    @1
    cF
    fveq2
    sseq1d
    imbi12d
    @40
    @45
    @42
    @46
    @43
    @9
    @17
    @1
    sseq2
    @40
    @12
    @18
    @4
    @41
    sseq2d
    imbi12d
    rspc2va
    syl21anc
    mpi
    unssd
    ralrimivva
    @20
    @14
    vc
    vd
    @7
    @7
    @10
    @8
    @9
    cun
    #
    @9
    wceq
    #
    @20
    @8
    @7
    wcel
    @9
    @7
    wcel
    wa
    #
    wa
    #
    @13
    @8
    @9
    ssequn1
    @51
    @49
    @13
    @51
    @49
    wa
    @11
    @48
    cF
    cfv
    #
    @12
    @51
    @11
    @52
    wss
    @49
    @51
    @11
    @12
    @52
    @50
    @20
    @11
    @12
    cun
    #
    @52
    wss
    #
    @19
    @54
    @11
    @4
    cun
    #
    @8
    @1
    cun
    #
    cF
    cfv
    #
    wss
    va
    vb
    @8
    @9
    @7
    @7
    @23
    @16
    @55
    @18
    @57
    @23
    @3
    @11
    @4
    @24
    uneq1d
    @23
    @17
    @56
    cF
    @0
    @8
    @1
    uneq1
    fveq2d
    sseq12d
    @25
    @55
    @53
    @57
    @52
    @25
    @4
    @12
    @11
    @26
    uneq2d
    @25
    @56
    @48
    cF
    @1
    @9
    @8
    uneq2
    fveq2d
    sseq12d
    rspc2va
    ancoms
    unssad
    adantr
    @49
    @52
    @12
    wceq
    @51
    @48
    @9
    cF
    fveq2
    adantl
    sseqtrd
    ex
    syl5bi
    ralrimivva
    impbii
    bitri
end
