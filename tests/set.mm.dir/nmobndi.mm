include "wf.mm"
include "cfv.mm"
include "cr.mm"
include "wcel.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wrex.mm"
include "c1.mm"
include "wi.mm"
include "wral.mm"
include "leid.mm"
include "breq2.mm"
include "rspcev.mm"
include "mpdan.mm"
include "wa.mm"
include "cxr.mm"
include "cmnf.mm"
include "clt.mm"
include "cnv.mm"
include "nmoxr.mm"
include "mp3an12.mm"
include "adantr.mm"
include "simprl.mm"
include "nmogtmnf.mm"
include "simprr.mm"
include "xrre.mm"
include "syl22anc.mm"
include "rexlimdvaa.mm"
include "impbid2.mm"
include "wb.mm"
include "rexr.mm"
include "nmoubi.mm"
include "sylan2.mm"
include "rexbidva.mm"
include "bitrd.mm"

theorem nmobndi
  let vy: setvar y
  let cT: class T
  let cU: class U
  let cL: class L
  let cM: class M
  let cN: class N
  let cW: class W
  let cX: class X
  let cY: class Y
  let vr: setvar r
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let vf: setvar f
  let vk: setvar k
  assume nmoubi.1: |- X = ( BaseSet ` U )
  assume nmoubi.y: |- Y = ( BaseSet ` W )
  assume nmoubi.l: |- L = ( normCV ` U )
  assume nmoubi.m: |- M = ( normCV ` W )
  assume nmoubi.3: |- N = ( U normOpOLD W )
  assume nmoubi.u: |- U e. NrmCVec
  assume nmoubi.w: |- W e. NrmCVec

  disjoint r y
  disjoint L r
  disjoint L y
  disjoint U y
  disjoint W y
  disjoint Y r
  disjoint Y y
  disjoint M r
  disjoint M y
  disjoint T r
  disjoint T y
  disjoint X r
  disjoint X y
  disjoint N r
  disjoint N y
  disjoint x z
  disjoint A x
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
  disjoint r z
  disjoint x y
  disjoint L x
  disjoint y z
  disjoint L z
  disjoint U x
  disjoint W x
  disjoint Y k
  disjoint Y x
  disjoint M f
  disjoint M k
  disjoint M x
  disjoint M z
  disjoint T f
  disjoint T k
  disjoint T x
  disjoint T z
  disjoint X f
  disjoint X k
  disjoint X x
  disjoint X z
  disjoint N k
  assert |- ( T : X --> Y -> ( ( N ` T ) e. RR <-> E. r e. RR A. y e. X ( ( L ` y ) <_ 1 -> ( M ` ( T ` y ) ) <_ r ) ) )

  proof
    cX
    cY
    cT
    wf
    #
    cT
    cN
    cfv
    #
    cr
    wcel
    #
    @1
    vr
    cv
    #
    cle
    wbr
    #
    vr
    cr
    wrex
    #
    vy
    cv
    #
    cL
    cfv
    c1
    cle
    wbr
    @6
    cT
    cfv
    cM
    cfv
    @3
    cle
    wbr
    wi
    vy
    cX
    wral
    #
    vr
    cr
    wrex
    @0
    @2
    @5
    @2
    @1
    @1
    cle
    wbr
    #
    @5
    @1
    leid
    @4
    @8
    vr
    @1
    cr
    @3
    @1
    @1
    cle
    breq2
    rspcev
    mpdan
    @0
    @4
    @2
    vr
    cr
    @0
    @3
    cr
    wcel
    #
    @4
    wa
    #
    wa
    @1
    cxr
    wcel
    #
    @9
    cmnf
    @1
    clt
    wbr
    #
    @4
    @2
    @0
    @11
    @10
    cU
    cnv
    wcel
    #
    cW
    cnv
    wcel
    #
    @0
    @11
    nmoubi.u
    nmoubi.w
    cT
    cU
    cN
    cW
    cX
    cY
    nmoubi.1
    nmoubi.y
    nmoubi.3
    nmoxr
    mp3an12
    adantr
    @0
    @9
    @4
    simprl
    @0
    @12
    @10
    @13
    @14
    @0
    @12
    nmoubi.u
    nmoubi.w
    cT
    cU
    cN
    cW
    cX
    cY
    nmoubi.1
    nmoubi.y
    nmoubi.3
    nmogtmnf
    mp3an12
    adantr
    @0
    @9
    @4
    simprr
    @1
    @3
    xrre
    syl22anc
    rexlimdvaa
    impbid2
    @0
    @4
    @7
    vr
    cr
    @9
    @0
    @3
    cxr
    wcel
    @4
    @7
    wb
    @3
    rexr
    vy
    @3
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
    nmoubi
    sylan2
    rexbidva
    bitrd
end
