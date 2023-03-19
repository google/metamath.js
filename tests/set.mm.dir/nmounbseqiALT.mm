include "wf.mm"
include "cfv.mm"
include "cpnf.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wrex.mm"
include "cr.mm"
include "wral.mm"
include "cn.mm"
include "wex.mm"
include "nmounbi.mm"
include "biimpa.mm"
include "wcel.mm"
include "nnre.mm"
include "imim1i.mm"
include "ralimi2.mm"
include "nnex.mm"
include "fveq2.mm"
include "breq1d.mm"
include "fveq2d.mm"
include "breq2d.mm"
include "anbi12d.mm"
include "ac6s.mm"
include "3syl.mm"

theorem nmounbseqiALT
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
  assert |- ( ( T : X --> Y /\ ( N ` T ) = +oo ) -> E. f ( f : NN --> X /\ A. k e. NN ( ( L ` ( f ` k ) ) <_ 1 /\ k < ( M ` ( T ` ( f ` k ) ) ) ) ) )

  proof
    cX
    cY
    cT
    wf
    #
    cT
    cN
    cfv
    cpnf
    wceq
    #
    wa
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
    vk
    cv
    #
    @2
    cT
    cfv
    #
    cM
    cfv
    #
    clt
    wbr
    #
    wa
    #
    vy
    cX
    wrex
    #
    vk
    cr
    wral
    #
    @10
    vk
    cn
    wral
    cn
    cX
    vf
    cv
    #
    wf
    @5
    @12
    cfv
    #
    cL
    cfv
    #
    c1
    cle
    wbr
    #
    @5
    @13
    cT
    cfv
    #
    cM
    cfv
    #
    clt
    wbr
    #
    wa
    #
    vk
    cn
    wral
    wa
    vf
    wex
    @0
    @1
    @11
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
    nmounbi
    biimpa
    @10
    @10
    vk
    cr
    cn
    @5
    cn
    wcel
    @5
    cr
    wcel
    @10
    @5
    nnre
    imim1i
    ralimi2
    @9
    @19
    vk
    vy
    cn
    cX
    vf
    nnex
    @2
    @13
    wceq
    #
    @4
    @15
    @8
    @18
    @20
    @3
    @14
    c1
    cle
    @2
    @13
    cL
    fveq2
    breq1d
    @20
    @7
    @17
    @5
    clt
    @20
    @6
    @16
    cM
    @2
    @13
    cT
    fveq2
    fveq2d
    breq2d
    anbi12d
    ac6s
    3syl
end
