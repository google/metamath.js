include "crelexp.mm"
include "cn.mm"
include "ctcl.mm"
include "dftrcl3.mm"
include "nnex.mm"
include "cun.mm"
include "unidm.mm"
include "eqcomi.mm"
include "cv.mm"
include "co.mm"
include "ciun.mm"
include "c1.mm"
include "csn.mm"
include "1ex.mm"
include "oveq2.mm"
include "iunxsn.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "ovex.mm"
include "iunex.mm"
include "relexp1g.mm"
include "ax-mp.mm"
include "cbviunv.mm"
include "eqtri.mm"
include "wss.mm"
include "1nn.mm"
include "snssi.mm"
include "iunss1.mm"
include "eqsstri.mm"
include "iunss.mm"
include "caddc.mm"
include "sseq1d.mm"
include "weq.mm"
include "eqimssi.mm"
include "wa.mm"
include "ccom.mm"
include "simpl.mm"
include "relexpsucnnr.mm"
include "sylancr.mm"
include "coss1.mm"
include "adantl.mm"
include "coeq2i.mm"
include "cfv.mm"
include "trclfvcotrg.mm"
include "vex.mm"
include "oveq1.mm"
include "iuneq2d.mm"
include "fvmpt.mm"
include "coeq12i.mm"
include "3sstr3i.mm"
include "syl6ss.mm"
include "eqsstrd.mm"
include "ex.mm"
include "nnind.mm"
include "mprgbir.mm"
include "iuneq1.mm"
include "sseqtri.mm"
include "comptiunov2i.mm"

theorem cotrcltrcl
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y


  assert |- ( t+ o. t+ ) = t+

  proof
    vi
    vj
    vk
    crelexp
    cn
    cn
    cn
    ctcl
    ctcl
    ctcl
    va
    vb
    vc
    vd
    vi
    va
    dftrcl3
    vj
    vb
    dftrcl3
    vk
    vc
    dftrcl3
    #
    nnex
    nnex
    cn
    cn
    cun
    #
    cn
    cn
    unidm
    eqcomi
    #
    vk
    cn
    vd
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
    vi
    c1
    csn
    #
    vj
    cn
    @3
    vj
    cv
    #
    crelexp
    co
    #
    ciun
    #
    vi
    cv
    #
    crelexp
    co
    #
    ciun
    #
    vi
    cn
    @12
    ciun
    #
    @13
    @6
    @13
    @10
    c1
    crelexp
    co
    #
    @6
    vi
    c1
    @12
    @15
    1ex
    @11
    c1
    @10
    crelexp
    oveq2
    iunxsn
    @15
    @10
    @6
    @10
    cvv
    wcel
    #
    @15
    @10
    wceq
    vj
    cn
    @9
    nnex
    @3
    @8
    crelexp
    ovex
    iunex
    #
    @10
    cvv
    relexp1g
    ax-mp
    vj
    vk
    cn
    @9
    @5
    @8
    @4
    @3
    crelexp
    oveq2
    cbviunv
    #
    eqtri
    #
    eqtri
    eqcomi
    @7
    cn
    wss
    #
    @13
    @14
    wss
    c1
    cn
    wcel
    @20
    1nn
    c1
    cn
    snssi
    ax-mp
    vi
    @7
    cn
    @12
    iunss1
    ax-mp
    eqsstri
    #
    @21
    @14
    @6
    vk
    @1
    @5
    ciun
    #
    @14
    @6
    wss
    @12
    @6
    wss
    #
    vi
    cn
    vi
    cn
    @12
    @6
    iunss
    @10
    vx
    cv
    #
    crelexp
    co
    #
    @6
    wss
    @15
    @6
    wss
    @10
    vy
    cv
    #
    crelexp
    co
    #
    @6
    wss
    #
    @10
    @26
    c1
    caddc
    co
    #
    crelexp
    co
    #
    @6
    wss
    #
    @23
    vx
    vy
    @11
    @24
    c1
    wceq
    @25
    @15
    @6
    @24
    c1
    @10
    crelexp
    oveq2
    sseq1d
    vx
    vy
    weq
    @25
    @27
    @6
    @24
    @26
    @10
    crelexp
    oveq2
    sseq1d
    @24
    @29
    wceq
    @25
    @30
    @6
    @24
    @29
    @10
    crelexp
    oveq2
    sseq1d
    vx
    vi
    weq
    @25
    @12
    @6
    @24
    @11
    @10
    crelexp
    oveq2
    sseq1d
    @15
    @6
    @19
    eqimssi
    @26
    cn
    wcel
    #
    @28
    @31
    @32
    @28
    wa
    #
    @30
    @27
    @10
    ccom
    #
    @6
    @33
    @16
    @32
    @30
    @34
    wceq
    @17
    @32
    @28
    simpl
    @10
    @26
    cvv
    relexpsucnnr
    sylancr
    @33
    @34
    @6
    @10
    ccom
    #
    @6
    @28
    @34
    @35
    wss
    @32
    @27
    @6
    @10
    coss1
    adantl
    @35
    @6
    @6
    ccom
    #
    @6
    @10
    @6
    @6
    @18
    coeq2i
    @3
    ctcl
    cfv
    #
    @37
    ccom
    @37
    @36
    @6
    @3
    trclfvcotrg
    @37
    @6
    @37
    @6
    @3
    cvv
    wcel
    @37
    @6
    wceq
    vd
    vex
    vc
    @3
    vk
    cn
    vc
    cv
    #
    @4
    crelexp
    co
    #
    ciun
    @6
    cvv
    ctcl
    vc
    vd
    weq
    vk
    cn
    @39
    @5
    @38
    @3
    @4
    crelexp
    oveq1
    iuneq2d
    @0
    vk
    cn
    @5
    nnex
    @3
    @4
    crelexp
    ovex
    iunex
    fvmpt
    ax-mp
    #
    @40
    coeq12i
    @40
    3sstr3i
    eqsstri
    syl6ss
    eqsstrd
    ex
    nnind
    mprgbir
    cn
    @1
    wceq
    @6
    @22
    wceq
    @2
    vk
    cn
    @1
    @5
    iuneq1
    ax-mp
    sseqtri
    comptiunov2i
end
