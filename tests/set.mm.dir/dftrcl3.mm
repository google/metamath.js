include "ctcl.mm"
include "cvv.mm"
include "cv.mm"
include "wss.mm"
include "ccom.mm"
include "wa.mm"
include "cab.mm"
include "cint.mm"
include "cmpt.mm"
include "cn.mm"
include "crelexp.mm"
include "co.mm"
include "ciun.mm"
include "df-trcl.mm"
include "wcel.mm"
include "cfv.mm"
include "c1.mm"
include "relexp1g.mm"
include "nnex.mm"
include "1nn.mm"
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
include "cuz.mm"
include "wceq.mm"
include "cn0.mm"
include "nnuz.mm"
include "1nn0.mm"
include "iunrelexpuztr.mm"
include "wb.mm"
include "wi.mm"
include "wal.mm"
include "fvex.mm"
include "trcleq2lem.mm"
include "a1i.mm"
include "alrimiv.mm"
include "elabgt.mm"
include "sylancr.mm"
include "mpbir2and.mm"
include "intss1.mm"
include "syl.mm"
include "wral.mm"
include "vex.mm"
include "elab.mm"
include "eqid.mm"
include "iunrelexpmin1.mm"
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

theorem dftrcl3
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
  assert |- t+ = ( r e. _V |-> U_ n e. NN ( r ^r n ) )

  proof
    ctcl
    vr
    cvv
    vr
    cv
    #
    vz
    cv
    #
    wss
    @1
    @1
    ccom
    @1
    wss
    wa
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
    cn
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
    df-trcl
    vr
    cvv
    @4
    @7
    @0
    cvv
    wcel
    #
    @4
    @0
    va
    cvv
    vn
    cn
    va
    cv
    #
    @5
    crelexp
    co
    #
    ciun
    #
    cmpt
    #
    cfv
    #
    @7
    @8
    @4
    @13
    @8
    @13
    @3
    wcel
    #
    @4
    @13
    wss
    @8
    @14
    @0
    @13
    wss
    #
    @13
    @13
    ccom
    @13
    wss
    #
    @8
    @0
    @0
    c1
    crelexp
    co
    #
    @13
    @0
    cvv
    relexp1g
    @8
    cn
    cvv
    wcel
    c1
    cn
    wcel
    @17
    @13
    wss
    nnex
    1nn
    @12
    @0
    cvv
    vk
    crelexp
    c1
    cn
    cvv
    vt
    va
    vt
    cvv
    @11
    vk
    cn
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
    @11
    vn
    cn
    @18
    @5
    crelexp
    co
    #
    ciun
    @21
    @22
    vn
    cn
    @10
    @23
    @9
    @18
    @5
    crelexp
    oveq1
    iuneq2d
    vn
    vk
    cn
    @23
    @20
    @5
    @19
    @18
    crelexp
    oveq2
    cbviunv
    syl6eq
    cbvmptv
    #
    ov2ssiunov2
    mp3an23
    eqsstr3d
    @8
    cn
    c1
    cuz
    cfv
    wceq
    c1
    cn0
    wcel
    @16
    nnuz
    1nn0
    @12
    @0
    vk
    c1
    cn
    cvv
    vt
    @24
    iunrelexpuztr
    mp3an23
    @8
    @13
    cvv
    wcel
    @1
    @13
    wceq
    @2
    @15
    @16
    wa
    #
    wb
    wi
    #
    vz
    wal
    @14
    @25
    wb
    @0
    @12
    fvex
    @8
    @26
    vz
    @26
    @8
    @1
    @13
    @0
    trcleq2lem
    a1i
    alrimiv
    @2
    @25
    vz
    @13
    cvv
    elabgt
    sylancr
    mpbir2and
    @13
    @3
    intss1
    syl
    @8
    @13
    vs
    cv
    #
    wss
    #
    vs
    @3
    wral
    @13
    @4
    wss
    @8
    @28
    vs
    @3
    @27
    @3
    wcel
    @0
    @27
    wss
    @27
    @27
    ccom
    @27
    wss
    wa
    #
    @8
    @28
    @2
    @29
    vz
    @27
    vs
    vex
    @1
    @27
    @0
    trcleq2lem
    elab
    @8
    @29
    @28
    wi
    #
    vs
    @8
    cn
    cn
    wceq
    @30
    vs
    wal
    cn
    eqid
    @12
    @0
    vk
    cn
    cvv
    vs
    vt
    @24
    iunrelexpmin1
    mpan2
    19.21bi
    syl5bi
    ralrimiv
    vs
    @13
    @3
    ssint
    sylibr
    eqssd
    va
    @0
    @11
    @7
    cvv
    @12
    va
    vr
    weq
    vn
    cn
    @10
    @6
    @9
    @0
    @5
    crelexp
    oveq1
    iuneq2d
    @12
    eqid
    vn
    cn
    @6
    nnex
    @0
    @5
    crelexp
    ovex
    iunex
    fvmpt
    eqtrd
    mpteq2ia
    eqtri
end
