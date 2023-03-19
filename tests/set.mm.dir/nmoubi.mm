include "wf.mm"
include "cxr.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "c1.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "wral.mm"
include "wi.mm"
include "clt.mm"
include "csup.mm"
include "wb.mm"
include "cnv.mm"
include "nmooval.mm"
include "mp3an12.mm"
include "breq1d.mm"
include "adantr.mm"
include "wss.mm"
include "cr.mm"
include "nmosetre.mm"
include "mpan.mm"
include "ressxr.mm"
include "syl6ss.mm"
include "supxrleub.mm"
include "sylan.mm"
include "bitrd.mm"
include "wal.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "ralab.mm"
include "ralcom4.mm"
include "ancomst.mm"
include "impexp.mm"
include "bitri.mm"
include "albii.mm"
include "fvex.mm"
include "breq1.mm"
include "imbi2d.mm"
include "ceqsalv.mm"
include "ralbii.mm"
include "r19.23v.mm"
include "3bitr3i.mm"
include "bitr4i.mm"
include "syl6bb.mm"

theorem nmoubi
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
  assert |- ( ( T : X --> Y /\ A e. RR* ) -> ( ( N ` T ) <_ A <-> A. x e. X ( ( L ` x ) <_ 1 -> ( M ` ( T ` x ) ) <_ A ) ) )

  proof
    cX
    cY
    cT
    wf
    #
    cA
    cxr
    wcel
    #
    wa
    #
    cT
    cN
    cfv
    #
    cA
    cle
    wbr
    #
    vz
    cv
    #
    cA
    cle
    wbr
    #
    vz
    vx
    cv
    #
    cL
    cfv
    c1
    cle
    wbr
    #
    vy
    cv
    #
    @7
    cT
    cfv
    #
    cM
    cfv
    #
    wceq
    #
    wa
    #
    vx
    cX
    wrex
    #
    vy
    cab
    #
    wral
    #
    @8
    @11
    cA
    cle
    wbr
    #
    wi
    #
    vx
    cX
    wral
    #
    @2
    @4
    @15
    cxr
    clt
    csup
    #
    cA
    cle
    wbr
    #
    @16
    @0
    @4
    @21
    wb
    @1
    @0
    @3
    @20
    cA
    cle
    cU
    cnv
    wcel
    cW
    cnv
    wcel
    #
    @0
    @3
    @20
    wceq
    nmoubi.u
    nmoubi.w
    vy
    vx
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
    nmooval
    mp3an12
    breq1d
    adantr
    @0
    @15
    cxr
    wss
    @1
    @21
    @16
    wb
    @0
    @15
    cr
    cxr
    @22
    @0
    @15
    cr
    wss
    nmoubi.w
    vy
    vx
    cT
    cL
    cM
    cW
    cX
    cY
    nmoubi.y
    nmoubi.m
    nmosetre
    mpan
    ressxr
    syl6ss
    vz
    @15
    cA
    supxrleub
    sylan
    bitrd
    @16
    @8
    @5
    @11
    wceq
    #
    wa
    #
    vx
    cX
    wrex
    #
    @6
    wi
    #
    vz
    wal
    #
    @19
    @14
    @25
    @6
    vz
    vy
    @9
    @5
    wceq
    #
    @13
    @24
    vx
    cX
    @28
    @12
    @23
    @8
    @9
    @5
    @11
    eqeq1
    anbi2d
    rexbidv
    ralab
    @24
    @6
    wi
    #
    vz
    wal
    #
    vx
    cX
    wral
    @29
    vx
    cX
    wral
    #
    vz
    wal
    @19
    @27
    @29
    vx
    vz
    cX
    ralcom4
    @30
    @18
    vx
    cX
    @30
    @23
    @8
    @6
    wi
    #
    wi
    #
    vz
    wal
    @18
    @29
    @33
    vz
    @29
    @23
    @8
    wa
    @6
    wi
    @33
    @8
    @23
    @6
    ancomst
    @23
    @8
    @6
    impexp
    bitri
    albii
    @32
    @18
    vz
    @11
    @10
    cM
    fvex
    @23
    @6
    @17
    @8
    @5
    @11
    cA
    cle
    breq1
    imbi2d
    ceqsalv
    bitri
    ralbii
    @31
    @26
    vz
    @24
    @6
    vx
    cX
    r19.23v
    albii
    3bitr3i
    bitr4i
    syl6bb
end
