include "crtcl.mm"
include "cvv.mm"
include "cid.mm"
include "cv.mm"
include "cdm.mm"
include "crn.mm"
include "cun.mm"
include "cres.mm"
include "wss.mm"
include "ccom.mm"
include "w3a.mm"
include "cab.mm"
include "cint.mm"
include "cmpt.mm"
include "cn0.mm"
include "crelexp.mm"
include "co.mm"
include "ciun.mm"
include "df-rtrcl.mm"
include "wcel.mm"
include "cfv.mm"
include "cc0.mm"
include "relexp0g.mm"
include "nn0ex.mm"
include "0nn0.mm"
include "weq.mm"
include "oveq1.mm"
include "iuneq2d.mm"
include "oveq2.mm"
include "cbviunv.mm"
include "syl6eq.mm"
include "cbvmptv.mm"
include "ov2ssiunov2.mm"
include "mp3an23.mm"
include "eqsstr3d.mm"
include "c1.mm"
include "relexp1g.mm"
include "1nn0.mm"
include "cuz.mm"
include "wceq.mm"
include "nn0uz.mm"
include "iunrelexpuztr.mm"
include "wb.mm"
include "wi.mm"
include "wal.mm"
include "fvex.mm"
include "sseq2.mm"
include "id.mm"
include "coeq12d.mm"
include "sseq12d.mm"
include "3anbi123d.mm"
include "a1i.mm"
include "alrimiv.mm"
include "elabgt.mm"
include "sylancr.mm"
include "mpbir3and.mm"
include "intss1.mm"
include "syl.mm"
include "wral.mm"
include "vex.mm"
include "elab.mm"
include "eqid.mm"
include "iunrelexpmin2.mm"
include "mpan2.mm"
include "19.21bi.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "ssint.mm"
include "sylibr.mm"
include "eqssd.mm"
include "ovex.mm"
include "iunex.mm"
include "fvmpt.mm"
include "eqtrd.mm"
include "mpteq2ia.mm"
include "eqtri.mm"

theorem dfrtrcl3
  let vn: setvar n
  let vr: setvar r
  let va: setvar a
  let vk: setvar k
  let vt: setvar t
  let vs: setvar s
  let vz: setvar z

  disjoint n r
  disjoint a k
  disjoint a t
  disjoint k t
  disjoint a n
  disjoint a r
  disjoint a s
  disjoint a z
  disjoint n s
  disjoint n z
  disjoint r s
  disjoint r z
  disjoint s z
  disjoint k n
  disjoint k r
  disjoint k s
  disjoint n t
  disjoint r t
  assert |- t* = ( r e. _V |-> U_ n e. NN0 ( r ^r n ) )

  proof
    crtcl
    vr
    cvv
    cid
    vr
    cv
    #
    cdm
    @0
    crn
    cun
    cres
    #
    vz
    cv
    #
    wss
    #
    @0
    @2
    wss
    #
    @2
    @2
    ccom
    #
    @2
    wss
    #
    w3a
    #
    vz
    cab
    #
    cint
    #
    cmpt
    vr
    cvv
    vn
    cn0
    @0
    vn
    cv
    #
    crelexp
    co
    #
    ciun
    #
    cmpt
    vr
    vz
    df-rtrcl
    vr
    cvv
    @9
    @12
    @0
    cvv
    wcel
    #
    @9
    @0
    va
    cvv
    vn
    cn0
    va
    cv
    #
    @10
    crelexp
    co
    #
    ciun
    #
    cmpt
    #
    cfv
    #
    @12
    @13
    @9
    @18
    @13
    @18
    @8
    wcel
    #
    @9
    @18
    wss
    @13
    @19
    @1
    @18
    wss
    #
    @0
    @18
    wss
    #
    @18
    @18
    ccom
    #
    @18
    wss
    #
    @13
    @1
    @0
    cc0
    crelexp
    co
    #
    @18
    @0
    cvv
    relexp0g
    @13
    cn0
    cvv
    wcel
    #
    cc0
    cn0
    wcel
    #
    @24
    @18
    wss
    nn0ex
    0nn0
    @17
    @0
    cvv
    vk
    crelexp
    cc0
    cn0
    cvv
    vt
    va
    vt
    cvv
    @16
    vk
    cn0
    vt
    cv
    #
    vk
    cv
    #
    crelexp
    co
    #
    ciun
    #
    va
    vt
    weq
    #
    @16
    vn
    cn0
    @27
    @10
    crelexp
    co
    #
    ciun
    @30
    @31
    vn
    cn0
    @15
    @32
    @14
    @27
    @10
    crelexp
    oveq1
    iuneq2d
    vn
    vk
    cn0
    @32
    @29
    @10
    @28
    @27
    crelexp
    oveq2
    cbviunv
    syl6eq
    cbvmptv
    #
    ov2ssiunov2
    mp3an23
    eqsstr3d
    @13
    @0
    @0
    c1
    crelexp
    co
    #
    @18
    @0
    cvv
    relexp1g
    @13
    @25
    c1
    cn0
    wcel
    @34
    @18
    wss
    nn0ex
    1nn0
    @17
    @0
    cvv
    vk
    crelexp
    c1
    cn0
    cvv
    vt
    @33
    ov2ssiunov2
    mp3an23
    eqsstr3d
    @13
    cn0
    cc0
    cuz
    cfv
    wceq
    @26
    @23
    nn0uz
    0nn0
    @17
    @0
    vk
    cc0
    cn0
    cvv
    vt
    @33
    iunrelexpuztr
    mp3an23
    @13
    @18
    cvv
    wcel
    @2
    @18
    wceq
    #
    @7
    @20
    @21
    @23
    w3a
    #
    wb
    wi
    #
    vz
    wal
    @19
    @36
    wb
    @0
    @17
    fvex
    @13
    @37
    vz
    @37
    @13
    @35
    @3
    @20
    @4
    @21
    @6
    @23
    @2
    @18
    @1
    sseq2
    @2
    @18
    @0
    sseq2
    @35
    @5
    @22
    @2
    @18
    @35
    @2
    @18
    @2
    @18
    @35
    id
    #
    @38
    coeq12d
    @38
    sseq12d
    3anbi123d
    a1i
    alrimiv
    @7
    @36
    vz
    @18
    cvv
    elabgt
    sylancr
    mpbir3and
    @18
    @8
    intss1
    syl
    @13
    @18
    vs
    cv
    #
    wss
    #
    vs
    @8
    wral
    @18
    @9
    wss
    @13
    @40
    vs
    @8
    @39
    @8
    wcel
    @1
    @39
    wss
    #
    @0
    @39
    wss
    #
    @39
    @39
    ccom
    #
    @39
    wss
    #
    w3a
    #
    @13
    @40
    @7
    @45
    vz
    @39
    vs
    vex
    vz
    vs
    weq
    #
    @3
    @41
    @4
    @42
    @6
    @44
    @2
    @39
    @1
    sseq2
    @2
    @39
    @0
    sseq2
    @46
    @5
    @43
    @2
    @39
    @46
    @2
    @39
    @2
    @39
    @46
    id
    #
    @47
    coeq12d
    @47
    sseq12d
    3anbi123d
    elab
    @13
    @45
    @40
    wi
    #
    vs
    @13
    cn0
    cn0
    wceq
    @48
    vs
    wal
    cn0
    eqid
    @17
    @0
    vk
    cn0
    cvv
    vs
    vt
    @33
    iunrelexpmin2
    mpan2
    19.21bi
    syl5bi
    ralrimiv
    vs
    @18
    @8
    ssint
    sylibr
    eqssd
    va
    @0
    @16
    @12
    cvv
    @17
    va
    vr
    weq
    vn
    cn0
    @15
    @11
    @14
    @0
    @10
    crelexp
    oveq1
    iuneq2d
    @17
    eqid
    vn
    cn0
    @11
    nn0ex
    @0
    @10
    crelexp
    ovex
    iunex
    fvmpt
    eqtrd
    mpteq2ia
    eqtri
end
