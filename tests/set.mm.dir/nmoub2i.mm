include "wf.mm"
include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "wral.mm"
include "w3a.mm"
include "cabs.mm"
include "nmoub3i.mm"
include "3adant2r.mm"
include "wceq.mm"
include "absid.mm"
include "3ad2ant2.mm"
include "breqtrd.mm"

theorem nmoub2i
  let vx: setvar x
  let cA: class A
  let cT: class T
  let cU: class U
  let cL: class L
  let cM: class M
  let cN: class N
  let cW: class W
  let cX: class X
  let cY: class Y
  let vz: setvar z
  let vf: setvar f
  let vk: setvar k
  let vr: setvar r
  let vy: setvar y
  assume nmoubi.1: |- X = ( BaseSet ` U )
  assume nmoubi.y: |- Y = ( BaseSet ` W )
  assume nmoubi.l: |- L = ( normCV ` U )
  assume nmoubi.m: |- M = ( normCV ` W )
  assume nmoubi.3: |- N = ( U normOpOLD W )
  assume nmoubi.u: |- U e. NrmCVec
  assume nmoubi.w: |- W e. NrmCVec

  disjoint A x
  disjoint L x
  disjoint U x
  disjoint W x
  disjoint Y x
  disjoint M x
  disjoint T x
  disjoint X x
  disjoint x z
  disjoint A z
  disjoint f k
  disjoint f r
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint L f
  disjoint k r
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint L k
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint L r
  disjoint x y
  disjoint y z
  disjoint L y
  disjoint L z
  disjoint U y
  disjoint W y
  disjoint Y k
  disjoint Y r
  disjoint Y y
  disjoint M f
  disjoint M k
  disjoint M r
  disjoint M y
  disjoint M z
  disjoint T f
  disjoint T k
  disjoint T r
  disjoint T y
  disjoint T z
  disjoint X f
  disjoint X k
  disjoint X r
  disjoint X y
  disjoint X z
  disjoint N k
  disjoint N r
  disjoint N y
  assert |- ( ( T : X --> Y /\ ( A e. RR /\ 0 <_ A ) /\ A. x e. X ( M ` ( T ` x ) ) <_ ( A x. ( L ` x ) ) ) -> ( N ` T ) <_ A )

  proof
    cX
    cY
    cT
    wf
    #
    cA
    cr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    wa
    #
    vx
    cv
    #
    cT
    cfv
    cM
    cfv
    cA
    @4
    cL
    cfv
    cmul
    co
    cle
    wbr
    vx
    cX
    wral
    #
    w3a
    cT
    cN
    cfv
    #
    cA
    cabs
    cfv
    #
    cA
    cle
    @0
    @1
    @5
    @6
    @7
    cle
    wbr
    @2
    vx
    cA
    cT
    cU
    cL
    cM
    cN
    cW
    cX
    cY
    nmoubi.1
    nmoubi.y
    nmoubi.l
    nmoubi.m
    nmoubi.3
    nmoubi.u
    nmoubi.w
    nmoub3i
    3adant2r
    @3
    @0
    @7
    cA
    wceq
    @5
    cA
    absid
    3ad2ant2
    breqtrd
end
