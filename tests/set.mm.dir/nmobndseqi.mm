include "wf.mm"
include "cn.mm"
include "cv.mm"
include "cfv.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "wi.mm"
include "wal.mm"
include "cr.mm"
include "wcel.mm"
include "impexp.mm"
include "r19.35.mm"
include "imbi2i.mm"
include "bitr4i.mm"
include "albii.mm"
include "wn.mm"
include "wex.mm"
include "cba.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "nnenom.mm"
include "wceq.mm"
include "fveq2.mm"
include "breq1d.mm"
include "fveq2d.mm"
include "imbi12d.mm"
include "notbid.mm"
include "axcc4.mm"
include "con3i.mm"
include "dfrex2.mm"
include "alinexa.mm"
include "bitri.mm"
include "dfral2.mm"
include "rexbii.mm"
include "rexnal.mm"
include "3imtr4i.mm"
include "nnre.mm"
include "anim1i.mm"
include "reximi2.mm"
include "syl.mm"
include "sylbi.mm"
include "nmobndi.mm"
include "syl5ibr.mm"
include "imp.mm"

theorem nmobndseqi
  let cT: class T
  let cU: class U
  let vf: setvar f
  let vk: setvar k
  let cL: class L
  let cM: class M
  let cN: class N
  let cW: class W
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let vr: setvar r
  let vy: setvar y
  assume nmoubi.1: |- X = ( BaseSet ` U )
  assume nmoubi.y: |- Y = ( BaseSet ` W )
  assume nmoubi.l: |- L = ( normCV ` U )
  assume nmoubi.m: |- M = ( normCV ` W )
  assume nmoubi.3: |- N = ( U normOpOLD W )
  assume nmoubi.u: |- U e. NrmCVec
  assume nmoubi.w: |- W e. NrmCVec

  disjoint f k
  disjoint L f
  disjoint L k
  disjoint Y k
  disjoint M f
  disjoint M k
  disjoint T f
  disjoint T k
  disjoint X f
  disjoint X k
  disjoint N k
  disjoint x z
  disjoint A x
  disjoint A z
  disjoint f r
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint k r
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint L r
  disjoint x y
  disjoint L x
  disjoint y z
  disjoint L y
  disjoint L z
  disjoint U x
  disjoint U y
  disjoint W x
  disjoint W y
  disjoint Y r
  disjoint Y x
  disjoint Y y
  disjoint M r
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint T r
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint X r
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint N r
  disjoint N y
  assert |- ( ( T : X --> Y /\ A. f ( ( f : NN --> X /\ A. k e. NN ( L ` ( f ` k ) ) <_ 1 ) -> E. k e. NN ( M ` ( T ` ( f ` k ) ) ) <_ k ) ) -> ( N ` T ) e. RR )

  proof
    cX
    cY
    cT
    wf
    #
    cn
    cX
    vf
    cv
    #
    wf
    #
    vk
    cv
    #
    @1
    cfv
    #
    cL
    cfv
    #
    c1
    cle
    wbr
    #
    vk
    cn
    wral
    #
    wa
    @4
    cT
    cfv
    #
    cM
    cfv
    #
    @3
    cle
    wbr
    #
    vk
    cn
    wrex
    #
    wi
    #
    vf
    wal
    #
    cT
    cN
    cfv
    cr
    wcel
    #
    @13
    @14
    @0
    vy
    cv
    #
    cL
    cfv
    #
    c1
    cle
    wbr
    #
    @15
    cT
    cfv
    #
    cM
    cfv
    #
    @3
    cle
    wbr
    #
    wi
    #
    vy
    cX
    wral
    #
    vk
    cr
    wrex
    #
    @13
    @2
    @6
    @10
    wi
    #
    vk
    cn
    wrex
    #
    wi
    #
    vf
    wal
    #
    @23
    @12
    @26
    vf
    @12
    @2
    @7
    @11
    wi
    #
    wi
    @26
    @2
    @7
    @11
    impexp
    @25
    @28
    @2
    @6
    @10
    vk
    cn
    r19.35
    imbi2i
    bitr4i
    albii
    @27
    @22
    vk
    cn
    wrex
    #
    @23
    @2
    @24
    wn
    #
    vk
    cn
    wral
    #
    wa
    vf
    wex
    #
    wn
    #
    @21
    wn
    #
    vy
    cX
    wrex
    #
    vk
    cn
    wral
    #
    wn
    #
    @27
    @29
    @36
    @32
    @34
    @30
    vy
    cX
    vf
    vk
    cn
    cX
    cU
    cba
    cfv
    cvv
    nmoubi.1
    cU
    cba
    fvex
    eqeltri
    nnenom
    @15
    @4
    wceq
    #
    @21
    @24
    @38
    @17
    @6
    @20
    @10
    @38
    @16
    @5
    c1
    cle
    @15
    @4
    cL
    fveq2
    breq1d
    @38
    @19
    @9
    @3
    cle
    @38
    @18
    @8
    cM
    @15
    @4
    cT
    fveq2
    fveq2d
    breq1d
    imbi12d
    notbid
    axcc4
    con3i
    @27
    @2
    @31
    wn
    #
    wi
    #
    vf
    wal
    @33
    @26
    @40
    vf
    @25
    @39
    @2
    @24
    vk
    cn
    dfrex2
    imbi2i
    albii
    @2
    @31
    vf
    alinexa
    bitri
    @29
    @35
    wn
    #
    vk
    cn
    wrex
    @37
    @22
    @41
    vk
    cn
    @21
    vy
    cX
    dfral2
    rexbii
    @35
    vk
    cn
    rexnal
    bitri
    3imtr4i
    @22
    @22
    vk
    cn
    cr
    @3
    cn
    wcel
    @3
    cr
    wcel
    @22
    @3
    nnre
    anim1i
    reximi2
    syl
    sylbi
    vy
    cT
    cU
    cL
    cM
    cN
    cW
    cX
    cY
    vk
    nmoubi.1
    nmoubi.y
    nmoubi.l
    nmoubi.m
    nmoubi.3
    nmoubi.u
    nmoubi.w
    nmobndi
    syl5ibr
    imp
end
