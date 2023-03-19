include "cnv.mm"
include "wcel.mm"
include "wa.mm"
include "caj.mm"
include "co.mm"
include "cv.mm"
include "wf.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "w3a.mm"
include "copab.mm"
include "cba.mm"
include "cdip.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "feq2d.mm"
include "feq3d.mm"
include "oveqd.mm"
include "eqeq2d.mm"
include "ralbidv.mm"
include "raleqbidv.mm"
include "3anbi123d.mm"
include "opabbidv.mm"
include "eqeq1d.mm"
include "df-aj.mm"
include "cmap.mm"
include "cxp.mm"
include "ovex.mm"
include "xpex.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "elmap.mm"
include "anbi12i.mm"
include "biimpri.mm"
include "3adant3.mm"
include "ssopab2i.mm"
include "df-xp.mm"
include "sseqtr4i.mm"
include "ssexi.mm"
include "ovmpt2.mm"
include "syl5eq.mm"

theorem ajfval
  let vx: setvar x
  let vy: setvar y
  let vt: setvar t
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cU: class U
  let cW: class W
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let vu: setvar u
  let vw: setvar w
  assume ajfval.1: |- X = ( BaseSet ` U )
  assume ajfval.2: |- Y = ( BaseSet ` W )
  assume ajfval.3: |- P = ( .iOLD ` U )
  assume ajfval.4: |- Q = ( .iOLD ` W )
  assume ajfval.5: |- A = ( U adj W )

  disjoint s t
  disjoint s x
  disjoint s y
  disjoint U s
  disjoint t x
  disjoint t y
  disjoint U t
  disjoint x y
  disjoint U x
  disjoint U y
  disjoint W s
  disjoint W t
  disjoint W x
  disjoint W y
  disjoint X s
  disjoint X t
  disjoint X x
  disjoint Y s
  disjoint Y t
  disjoint Y y
  disjoint u w
  disjoint P u
  disjoint P w
  disjoint s u
  disjoint s w
  disjoint t u
  disjoint t w
  disjoint u x
  disjoint u y
  disjoint U u
  disjoint w x
  disjoint w y
  disjoint U w
  disjoint W u
  disjoint W w
  disjoint X u
  disjoint X w
  disjoint Q u
  disjoint Q w
  disjoint Y u
  disjoint Y w
  assert |- ( ( U e. NrmCVec /\ W e. NrmCVec ) -> A = { <. t , s >. | ( t : X --> Y /\ s : Y --> X /\ A. x e. X A. y e. Y ( ( t ` x ) Q y ) = ( x P ( s ` y ) ) ) } )

  proof
    cU
    cnv
    wcel
    cW
    cnv
    wcel
    wa
    cA
    cU
    cW
    caj
    co
    cX
    cY
    vt
    cv
    #
    wf
    #
    cY
    cX
    vs
    cv
    #
    wf
    #
    vx
    cv
    #
    @0
    cfv
    #
    vy
    cv
    #
    cQ
    co
    #
    @4
    @6
    @2
    cfv
    #
    cP
    co
    #
    wceq
    #
    vy
    cY
    wral
    #
    vx
    cX
    wral
    #
    w3a
    #
    vt
    vs
    copab
    #
    ajfval.5
    vu
    vw
    cU
    cW
    cnv
    cnv
    vu
    cv
    #
    cba
    cfv
    #
    vw
    cv
    #
    cba
    cfv
    #
    @0
    wf
    #
    @18
    @16
    @2
    wf
    #
    @5
    @6
    @17
    cdip
    cfv
    #
    co
    #
    @4
    @8
    @15
    cdip
    cfv
    #
    co
    #
    wceq
    #
    vy
    @18
    wral
    #
    vx
    @16
    wral
    #
    w3a
    #
    vt
    vs
    copab
    @14
    caj
    cX
    @18
    @0
    wf
    #
    @18
    cX
    @2
    wf
    #
    @22
    @9
    wceq
    #
    vy
    @18
    wral
    #
    vx
    cX
    wral
    #
    w3a
    #
    vt
    vs
    copab
    @15
    cU
    wceq
    #
    @28
    @34
    vt
    vs
    @35
    @19
    @29
    @20
    @30
    @27
    @33
    @35
    @16
    cX
    @18
    @0
    @35
    @16
    cU
    cba
    cfv
    #
    cX
    @15
    cU
    cba
    fveq2
    ajfval.1
    syl6eqr
    #
    feq2d
    @35
    @16
    cX
    @2
    @18
    @37
    feq3d
    @35
    @26
    @32
    vx
    @16
    cX
    @37
    @35
    @25
    @31
    vy
    @18
    @35
    @24
    @9
    @22
    @35
    @23
    cP
    @4
    @8
    @35
    @23
    cU
    cdip
    cfv
    cP
    @15
    cU
    cdip
    fveq2
    ajfval.3
    syl6eqr
    oveqd
    eqeq2d
    ralbidv
    raleqbidv
    3anbi123d
    opabbidv
    @17
    cW
    wceq
    #
    @34
    @13
    vt
    vs
    @38
    @29
    @1
    @30
    @3
    @33
    @12
    @38
    @18
    cY
    @0
    cX
    @38
    @18
    cW
    cba
    cfv
    #
    cY
    @17
    cW
    cba
    fveq2
    ajfval.2
    syl6eqr
    #
    feq3d
    @38
    @18
    cY
    cX
    @2
    @40
    feq2d
    @38
    @32
    @11
    vx
    cX
    @38
    @31
    @10
    vy
    @18
    cY
    @40
    @38
    @22
    @7
    @9
    @38
    @21
    cQ
    @5
    @6
    @38
    @21
    cW
    cdip
    cfv
    cQ
    @17
    cW
    cdip
    fveq2
    ajfval.4
    syl6eqr
    oveqd
    eqeq1d
    raleqbidv
    ralbidv
    3anbi123d
    opabbidv
    vx
    vy
    vw
    vu
    vt
    vs
    df-aj
    @14
    cY
    cX
    cmap
    co
    #
    cX
    cY
    cmap
    co
    #
    cxp
    #
    @41
    @42
    cY
    cX
    cmap
    ovex
    cX
    cY
    cmap
    ovex
    xpex
    @14
    @0
    @41
    wcel
    #
    @2
    @42
    wcel
    #
    wa
    #
    vt
    vs
    copab
    @43
    @13
    @46
    vt
    vs
    @1
    @3
    @46
    @12
    @46
    @1
    @3
    wa
    @44
    @1
    @45
    @3
    cY
    cX
    @0
    cY
    @39
    cvv
    ajfval.2
    cW
    cba
    fvex
    eqeltri
    #
    cX
    @36
    cvv
    ajfval.1
    cU
    cba
    fvex
    eqeltri
    #
    elmap
    cX
    cY
    @2
    @48
    @47
    elmap
    anbi12i
    biimpri
    3adant3
    ssopab2i
    vt
    vs
    @41
    @42
    df-xp
    sseqtr4i
    ssexi
    ovmpt2
    syl5eq
end
