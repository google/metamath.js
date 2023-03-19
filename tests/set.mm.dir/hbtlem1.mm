include "wcel.mm"
include "cn0.mm"
include "w3a.mm"
include "cfv.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cco1.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "cab.mm"
include "cmpt.mm"
include "cldgis.mm"
include "cvv.mm"
include "elex.mm"
include "cpl1.mm"
include "clidl.mm"
include "cdg1.mm"
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
include "syl.mm"
include "syl5eq.mm"
include "3ad2ant1.mm"
include "rexeq.mm"
include "eqid.mm"
include "nn0ex.mm"
include "3ad2ant2.mm"
include "simp3.mm"
include "wss.mm"
include "simpr.mm"
include "reximi.mm"
include "ss2abi.mm"
include "abrexexg.mm"
include "ssexg.mm"
include "sylancr.mm"
include "breq2.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "fvmptg.mm"
include "syl2anc.mm"
include "3eqtrd.mm"

theorem hbtlem1
  let cD: class D
  let cP: class P
  let cR: class R
  let cS: class S
  let cU: class U
  let vj: setvar j
  let vk: setvar k
  let cI: class I
  let cV: class V
  let cX: class X
  let vi: setvar i
  let vr: setvar r
  let vx: setvar x
  assume hbtlem.p: |- P = ( Poly1 ` R )
  assume hbtlem.u: |- U = ( LIdeal ` P )
  assume hbtlem.s: |- S = ( ldgIdlSeq ` R )
  assume hbtlem.d: |- D = ( deg1 ` R )

  disjoint I j
  disjoint I k
  disjoint j k
  disjoint R j
  disjoint R k
  disjoint X j
  disjoint X k
  disjoint D i
  disjoint D r
  disjoint D x
  disjoint i r
  disjoint i x
  disjoint r x
  disjoint I i
  disjoint I x
  disjoint i j
  disjoint i k
  disjoint j x
  disjoint k x
  disjoint R i
  disjoint R r
  disjoint R x
  disjoint j r
  disjoint k r
  disjoint U i
  disjoint U r
  disjoint X x
  assert |- ( ( R e. V /\ I e. U /\ X e. NN0 ) -> ( ( S ` I ) ` X ) = { j | E. k e. I ( ( D ` k ) <_ X /\ j = ( ( coe1 ` k ) ` X ) ) } )

  proof
    cR
    cV
    wcel
    #
    cI
    cU
    wcel
    #
    cX
    cn0
    wcel
    #
    w3a
    #
    cX
    cI
    cS
    cfv
    #
    cfv
    #
    cX
    cI
    vi
    cU
    vx
    cn0
    vk
    cv
    #
    cD
    cfv
    #
    vx
    cv
    #
    cle
    wbr
    #
    vj
    cv
    #
    @8
    @6
    cco1
    cfv
    #
    cfv
    #
    wceq
    #
    wa
    #
    vk
    vi
    cv
    #
    wrex
    #
    vj
    cab
    #
    cmpt
    #
    cmpt
    #
    cfv
    #
    cfv
    #
    cX
    vx
    cn0
    @14
    vk
    cI
    wrex
    #
    vj
    cab
    #
    cmpt
    #
    cfv
    #
    @7
    cX
    cle
    wbr
    #
    @10
    cX
    @11
    cfv
    #
    wceq
    #
    wa
    #
    vk
    cI
    wrex
    #
    vj
    cab
    #
    @0
    @1
    @5
    @21
    wceq
    @2
    @0
    cX
    @4
    @20
    @0
    cI
    cS
    @19
    @0
    cS
    cR
    cldgis
    cfv
    #
    @19
    hbtlem.s
    @0
    cR
    cvv
    wcel
    @32
    @19
    wceq
    cR
    cV
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
    @6
    @33
    cdg1
    cfv
    #
    cfv
    #
    @8
    cle
    wbr
    #
    @13
    wa
    #
    vk
    @15
    wrex
    #
    vj
    cab
    #
    cmpt
    #
    cmpt
    @19
    cvv
    cldgis
    @33
    cR
    wceq
    #
    vi
    @35
    @42
    cU
    @18
    @43
    @35
    cP
    clidl
    cfv
    #
    cU
    @43
    @34
    cP
    clidl
    @43
    @34
    cR
    cpl1
    cfv
    cP
    @33
    cR
    cpl1
    fveq2
    hbtlem.p
    syl6eqr
    fveq2d
    hbtlem.u
    syl6eqr
    @43
    vx
    cn0
    @41
    @17
    @43
    @40
    @16
    vj
    @43
    @39
    @14
    vk
    @15
    @43
    @38
    @9
    @13
    @43
    @37
    @7
    @8
    cle
    @43
    @6
    @36
    cD
    @43
    @36
    cR
    cdg1
    cfv
    cD
    @33
    cR
    cdg1
    fveq2
    hbtlem.d
    syl6eqr
    fveq1d
    breq1d
    anbi1d
    rexbidv
    abbidv
    mpteq2dv
    mpteq12dv
    vx
    vi
    vj
    vk
    vr
    df-ldgis
    vi
    cU
    @18
    cU
    @44
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
    fveq1d
    3ad2ant1
    @1
    @0
    @21
    @25
    wceq
    @2
    @1
    cX
    @20
    @24
    vi
    cI
    @18
    @24
    cU
    @19
    @15
    cI
    wceq
    #
    vx
    cn0
    @17
    @23
    @45
    @16
    @22
    vj
    @14
    vk
    @15
    cI
    rexeq
    abbidv
    mpteq2dv
    @19
    eqid
    vx
    cn0
    @23
    nn0ex
    mptex
    fvmpt
    fveq1d
    3ad2ant2
    @3
    @2
    @31
    cvv
    wcel
    #
    @25
    @31
    wceq
    @0
    @1
    @2
    simp3
    @3
    @31
    @28
    vk
    cI
    wrex
    #
    vj
    cab
    #
    wss
    @48
    cvv
    wcel
    #
    @46
    @30
    @47
    vj
    @29
    @28
    vk
    cI
    @26
    @28
    simpr
    reximi
    ss2abi
    @1
    @0
    @49
    @2
    vk
    vj
    cI
    @27
    cU
    abrexexg
    3ad2ant2
    @31
    @48
    cvv
    ssexg
    sylancr
    vx
    cX
    @23
    @31
    cn0
    cvv
    @24
    @8
    cX
    wceq
    #
    @22
    @30
    vj
    @50
    @14
    @29
    vk
    cI
    @50
    @9
    @26
    @13
    @28
    @8
    cX
    @7
    cle
    breq2
    @50
    @12
    @27
    @10
    @8
    cX
    @11
    fveq2
    eqeq2d
    anbi12d
    rexbidv
    abbidv
    @24
    eqid
    fvmptg
    syl2anc
    3eqtrd
end
