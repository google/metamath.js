include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wa.mm"
include "wrex.mm"
include "cr.mm"
include "wral.mm"
include "cpnf.mm"
include "wcel.mm"
include "wi.mm"
include "wne.mm"
include "wn.mm"
include "nmobndi.mm"
include "cnv.mm"
include "wb.mm"
include "nmorepnf.mm"
include "mp3an12.mm"
include "ffvelrn.mm"
include "nvcl.mm"
include "sylancr.mm"
include "lenlt.mm"
include "sylan.mm"
include "an32s.mm"
include "imbi2d.mm"
include "imnan.mm"
include "syl6bb.mm"
include "ralbidva.mm"
include "ralnex.mm"
include "rexbidva.mm"
include "rexnal.mm"
include "3bitr3d.mm"
include "necon4abid.mm"

theorem nmounbi
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
  assert |- ( T : X --> Y -> ( ( N ` T ) = +oo <-> A. r e. RR E. y e. X ( ( L ` y ) <_ 1 /\ r < ( M ` ( T ` y ) ) ) ) )

  proof
    cX
    cY
    cT
    wf
    #
    vy
    cv
    #
    cL
    cfv
    c1
    cle
    wbr
    #
    vr
    cv
    #
    @1
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
    vr
    cr
    wral
    #
    cT
    cN
    cfv
    #
    cpnf
    @0
    @10
    cr
    wcel
    #
    @2
    @5
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
    vr
    cr
    wrex
    #
    @10
    cpnf
    wne
    #
    @9
    wn
    #
    vy
    cT
    cU
    cL
    cM
    cN
    cW
    cX
    cY
    vr
    nmoubi.1
    nmoubi.y
    nmoubi.l
    nmoubi.m
    nmoubi.3
    nmoubi.u
    nmoubi.w
    nmobndi
    cU
    cnv
    wcel
    cW
    cnv
    wcel
    #
    @0
    @11
    @16
    wb
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
    nmorepnf
    mp3an12
    @0
    @15
    @8
    wn
    #
    vr
    cr
    wrex
    @17
    @0
    @14
    @19
    vr
    cr
    @0
    @3
    cr
    wcel
    #
    wa
    #
    @14
    @7
    wn
    #
    vy
    cX
    wral
    @19
    @21
    @13
    @22
    vy
    cX
    @21
    @1
    cX
    wcel
    #
    wa
    #
    @13
    @2
    @6
    wn
    #
    wi
    @22
    @24
    @12
    @25
    @2
    @0
    @23
    @20
    @12
    @25
    wb
    #
    @0
    @23
    wa
    #
    @5
    cr
    wcel
    #
    @20
    @26
    @27
    @18
    @4
    cY
    wcel
    @28
    nmoubi.w
    cX
    cY
    @1
    cT
    ffvelrn
    @4
    cW
    cM
    cY
    nmoubi.y
    nmoubi.m
    nvcl
    sylancr
    @5
    @3
    lenlt
    sylan
    an32s
    imbi2d
    @2
    @6
    imnan
    syl6bb
    ralbidva
    @7
    vy
    cX
    ralnex
    syl6bb
    rexbidva
    @8
    vr
    cr
    rexnal
    syl6bb
    3bitr3d
    necon4abid
end
