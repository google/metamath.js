include "cv.mm"
include "wss.mm"
include "cfv.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "cin.mm"
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
include "inss1.mm"
include "inss2.mm"
include "elpwi.mm"
include "syl5ss.mm"
include "vex.mm"
include "inex2.mm"
include "elpw.mm"
include "sylibr.mm"
include "ad2antll.mm"
include "simprl.mm"
include "simpl.mm"
include "wceq.mm"
include "rspc2va.mm"
include "syl21anc.mm"
include "mpi.mm"
include "simprr.mm"
include "ssind.mm"
include "ralrimivva.mm"
include "dfss.mm"
include "adantl.mm"
include "ineq1.mm"
include "fveq2d.mm"
include "ineq1d.mm"
include "sseq12d.mm"
include "ineq2.mm"
include "ineq2d.mm"
include "ancoms.mm"
include "syl6ss.mm"
include "adantr.mm"
include "eqsstrd.mm"
include "ex.mm"
include "syl5bi.mm"
include "impbii.mm"
include "bitri.mm"

theorem isotone2
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
  assert |- ( A. a e. ~P A A. b e. ~P A ( a C_ b -> ( F ` a ) C_ ( F ` b ) ) <-> A. a e. ~P A A. b e. ~P A ( F ` ( a i^i b ) ) C_ ( ( F ` a ) i^i ( F ` b ) ) )

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
    @0
    @1
    cin
    #
    cF
    cfv
    #
    @3
    @4
    cin
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
    @17
    @3
    @4
    @30
    @16
    @0
    wss
    #
    @17
    @3
    wss
    #
    @0
    @1
    inss1
    @30
    @16
    @7
    wcel
    #
    @27
    @15
    @31
    @32
    wi
    #
    @28
    @33
    @15
    @27
    @28
    @16
    cA
    wss
    @33
    @28
    @16
    @1
    cA
    @0
    @1
    inss2
    #
    @1
    cA
    elpwi
    syl5ss
    @16
    cA
    @1
    @0
    vb
    vex
    inex2
    elpw
    sylibr
    ad2antll
    #
    @15
    @27
    @28
    simprl
    @15
    @29
    simpl
    #
    @14
    @34
    @16
    @9
    wss
    #
    @17
    @12
    wss
    #
    wi
    #
    vc
    vd
    @16
    @0
    @7
    @7
    @8
    @16
    wceq
    #
    @10
    @38
    @13
    @39
    @8
    @16
    @9
    sseq1
    @41
    @11
    @17
    @12
    @8
    @16
    cF
    fveq2
    sseq1d
    imbi12d
    #
    vd
    va
    weq
    #
    @38
    @31
    @39
    @32
    @9
    @0
    @16
    sseq2
    @43
    @12
    @3
    @17
    @9
    @0
    cF
    fveq2
    sseq2d
    imbi12d
    rspc2va
    syl21anc
    mpi
    @30
    @16
    @1
    wss
    #
    @17
    @4
    wss
    #
    @35
    @30
    @33
    @28
    @15
    @44
    @45
    wi
    #
    @36
    @15
    @27
    @28
    simprr
    @37
    @14
    @46
    @40
    vc
    vd
    @16
    @1
    @7
    @7
    @42
    vd
    vb
    weq
    #
    @38
    @44
    @39
    @45
    @9
    @1
    @16
    sseq2
    @47
    @12
    @4
    @17
    @9
    @1
    cF
    fveq2
    sseq2d
    imbi12d
    rspc2va
    syl21anc
    mpi
    ssind
    ralrimivva
    @20
    @14
    vc
    vd
    @7
    @7
    @10
    @8
    @8
    @9
    cin
    #
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
    dfss
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
    @49
    @11
    @52
    wceq
    @51
    @8
    @48
    cF
    fveq2
    adantl
    @51
    @52
    @12
    wss
    @49
    @51
    @52
    @11
    @12
    cin
    #
    @12
    @50
    @20
    @52
    @53
    wss
    #
    @19
    @54
    @8
    @1
    cin
    #
    cF
    cfv
    #
    @11
    @4
    cin
    #
    wss
    va
    vb
    @8
    @9
    @7
    @7
    @23
    @17
    @56
    @18
    @57
    @23
    @16
    @55
    cF
    @0
    @8
    @1
    ineq1
    fveq2d
    @23
    @3
    @11
    @4
    @24
    ineq1d
    sseq12d
    @25
    @56
    @52
    @57
    @53
    @25
    @55
    @48
    cF
    @1
    @9
    @8
    ineq2
    fveq2d
    @25
    @4
    @12
    @11
    @26
    ineq2d
    sseq12d
    rspc2va
    ancoms
    @11
    @12
    inss2
    syl6ss
    adantr
    eqsstrd
    ex
    syl5bi
    ralrimivva
    impbii
    bitri
end
