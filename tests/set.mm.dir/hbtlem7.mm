include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cn0.mm"
include "wfn.mm"
include "cv.mm"
include "wral.mm"
include "wf.mm"
include "cdg1.mm"
include "cle.mm"
include "wbr.mm"
include "cco1.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "cmpt.mm"
include "cvv.mm"
include "wss.mm"
include "simpr.mm"
include "reximi.mm"
include "ss2abi.mm"
include "abrexexg.mm"
include "ssexg.mm"
include "sylancr.mm"
include "ralrimivw.mm"
include "adantl.mm"
include "eqid.mm"
include "fnmpt.mm"
include "syl.mm"
include "cldgis.mm"
include "elex.mm"
include "cpl1.mm"
include "clidl.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "breq1d.mm"
include "anbi1d.mm"
include "rexbidv.mm"
include "abbidv.mm"
include "mpteq2dv.mm"
include "mpteq12dv.mm"
include "df-ldgis.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "fvmpt.mm"
include "syl5eq.mm"
include "rexeq.mm"
include "nn0ex.mm"
include "sylan9eq.mm"
include "fneq1d.mm"
include "mpbird.mm"
include "hbtlem2.mm"
include "3expa.mm"
include "ralrimiva.mm"
include "ffnfv.mm"
include "sylanbrc.mm"

theorem hbtlem7
  let cP: class P
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cI: class I
  let vi: setvar i
  let vj: setvar j
  let vx: setvar x
  let vy: setvar y
  let vr: setvar r
  assume hbtlem.p: |- P = ( Poly1 ` R )
  assume hbtlem.u: |- U = ( LIdeal ` P )
  assume hbtlem.s: |- S = ( ldgIdlSeq ` R )
  assume hbtlem7.t: |- T = ( LIdeal ` R )


  assert |- ( ( R e. Ring /\ I e. U ) -> ( S ` I ) : NN0 --> T )

  proof
    cR
    crg
    wcel
    #
    cI
    cU
    wcel
    #
    wa
    #
    cI
    cS
    cfv
    #
    cn0
    wfn
    #
    vx
    cv
    #
    @3
    cfv
    cT
    wcel
    #
    vx
    cn0
    wral
    cn0
    cT
    @3
    wf
    @2
    @4
    vx
    cn0
    vj
    cv
    #
    cR
    cdg1
    cfv
    #
    cfv
    #
    @5
    cle
    wbr
    #
    vy
    cv
    @5
    @7
    cco1
    cfv
    cfv
    #
    wceq
    #
    wa
    #
    vj
    cI
    wrex
    #
    vy
    cab
    #
    cmpt
    #
    cn0
    wfn
    #
    @2
    @15
    cvv
    wcel
    #
    vx
    cn0
    wral
    #
    @17
    @1
    @19
    @0
    @1
    @18
    vx
    cn0
    @1
    @15
    @12
    vj
    cI
    wrex
    #
    vy
    cab
    #
    wss
    @21
    cvv
    wcel
    @18
    @14
    @20
    vy
    @13
    @12
    vj
    cI
    @10
    @12
    simpr
    reximi
    ss2abi
    vj
    vy
    cI
    @11
    cU
    abrexexg
    @15
    @21
    cvv
    ssexg
    sylancr
    ralrimivw
    adantl
    vx
    cn0
    @15
    @16
    cvv
    @16
    eqid
    fnmpt
    syl
    @2
    cn0
    @3
    @16
    @0
    @1
    @3
    cI
    vi
    cU
    vx
    cn0
    @13
    vj
    vi
    cv
    #
    wrex
    #
    vy
    cab
    #
    cmpt
    #
    cmpt
    #
    cfv
    @16
    @0
    cI
    cS
    @26
    @0
    cS
    cR
    cldgis
    cfv
    #
    @26
    hbtlem.s
    @0
    cR
    cvv
    wcel
    @27
    @26
    wceq
    cR
    crg
    elex
    vr
    cR
    vi
    vr
    cv
    #
    cpl1
    cfv
    #
    clidl
    cfv
    #
    vx
    cn0
    @7
    @28
    cdg1
    cfv
    #
    cfv
    #
    @5
    cle
    wbr
    #
    @12
    wa
    #
    vj
    @22
    wrex
    #
    vy
    cab
    #
    cmpt
    #
    cmpt
    @26
    cvv
    cldgis
    @28
    cR
    wceq
    #
    vi
    @30
    @37
    cU
    @25
    @38
    @30
    cP
    clidl
    cfv
    #
    cU
    @38
    @29
    cP
    clidl
    @38
    @29
    cR
    cpl1
    cfv
    cP
    @28
    cR
    cpl1
    fveq2
    hbtlem.p
    syl6eqr
    fveq2d
    hbtlem.u
    syl6eqr
    @38
    vx
    cn0
    @36
    @24
    @38
    @35
    @23
    vy
    @38
    @34
    @13
    vj
    @22
    @38
    @33
    @10
    @12
    @38
    @32
    @9
    @5
    cle
    @38
    @7
    @31
    @8
    @28
    cR
    cdg1
    fveq2
    fveq1d
    breq1d
    anbi1d
    rexbidv
    abbidv
    mpteq2dv
    mpteq12dv
    vx
    vi
    vy
    vj
    vr
    df-ldgis
    vi
    cU
    @25
    cU
    @39
    cvv
    hbtlem.u
    cP
    clidl
    fvex
    eqeltri
    mptex
    fvmpt
    syl
    syl5eq
    fveq1d
    vi
    cI
    @25
    @16
    cU
    @26
    @22
    cI
    wceq
    #
    vx
    cn0
    @24
    @15
    @40
    @23
    @14
    vy
    @13
    vj
    @22
    cI
    rexeq
    abbidv
    mpteq2dv
    @26
    eqid
    vx
    cn0
    @15
    nn0ex
    mptex
    fvmpt
    sylan9eq
    fneq1d
    mpbird
    @2
    @6
    vx
    cn0
    @0
    @1
    @5
    cn0
    wcel
    @6
    cP
    cR
    cS
    cT
    cU
    cI
    @5
    hbtlem.p
    hbtlem.u
    hbtlem.s
    hbtlem7.t
    hbtlem2
    3expa
    ralrimiva
    vx
    cn0
    cT
    @3
    ffnfv
    sylanbrc
end
