include "wcel.mm"
include "w3a.mm"
include "cvv.mm"
include "crab.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "wceq.mm"
include "a1i.mm"
include "cv.mm"
include "wa.mm"
include "rabeqbidv.mm"
include "mpteq12dv.mm"
include "adantl.mm"
include "eqidd.mm"
include "elex.mm"
include "3ad2ant1.mm"
include "3ad2ant2.mm"
include "mptexg.mm"
include "3ad2ant3.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfrab.mm"
include "nfmpt.mm"
include "ovmpt2dxf.mm"

theorem ovmpt3rab1
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cU: class U
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cO: class O
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let va: setvar a
  assume ovmpt3rab1.o: |- O = ( x e. _V , y e. _V |-> ( z e. M |-> { a e. N | ph } ) )
  assume ovmpt3rab1.m: |- ( ( x = X /\ y = Y ) -> M = K )
  assume ovmpt3rab1.n: |- ( ( x = X /\ y = Y ) -> N = L )
  assume ovmpt3rab1.p: |- ( ( x = X /\ y = Y ) -> ( ph <-> ps ) )
  assume ovmpt3rab1.x: |- F/ x ps
  assume ovmpt3rab1.y: |- F/ y ps

  disjoint K x
  disjoint K y
  disjoint K z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint L a
  disjoint L x
  disjoint L y
  disjoint a x
  disjoint a y
  disjoint N a
  disjoint V x
  disjoint V y
  disjoint W x
  disjoint W y
  disjoint U x
  disjoint U y
  disjoint X a
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint a z
  disjoint Y a
  disjoint Y x
  disjoint Y y
  disjoint Y z
  assert |- ( ( X e. V /\ Y e. W /\ K e. U ) -> ( X O Y ) = ( z e. K |-> { a e. L | ps } ) )

  proof
    cX
    cV
    wcel
    #
    cY
    cW
    wcel
    #
    cK
    cU
    wcel
    #
    w3a
    #
    vx
    vy
    cX
    cY
    cvv
    cvv
    vz
    cM
    wph
    va
    cN
    crab
    #
    cmpt
    #
    vz
    cK
    wps
    va
    cL
    crab
    #
    cmpt
    #
    cO
    cvv
    cvv
    cO
    vx
    vy
    cvv
    cvv
    @5
    cmpt2
    wceq
    @3
    ovmpt3rab1.o
    a1i
    vx
    cv
    cX
    wceq
    #
    vy
    cv
    cY
    wceq
    wa
    #
    @5
    @7
    wceq
    @3
    @9
    vz
    cM
    @4
    cK
    @6
    ovmpt3rab1.m
    @9
    wph
    wps
    va
    cN
    cL
    ovmpt3rab1.n
    ovmpt3rab1.p
    rabeqbidv
    mpteq12dv
    adantl
    @3
    @8
    wa
    cvv
    eqidd
    @0
    @1
    cX
    cvv
    wcel
    @2
    cX
    cV
    elex
    3ad2ant1
    @1
    @0
    cY
    cvv
    wcel
    @2
    cY
    cW
    elex
    3ad2ant2
    @2
    @0
    @7
    cvv
    wcel
    @1
    vz
    cK
    @6
    cU
    mptexg
    3ad2ant3
    @3
    vx
    nfv
    @3
    vy
    nfv
    vy
    cX
    nfcv
    vx
    cY
    nfcv
    vx
    vz
    cK
    @6
    vx
    cK
    nfcv
    wps
    vx
    va
    cL
    ovmpt3rab1.x
    vx
    cL
    nfcv
    nfrab
    nfmpt
    vy
    vz
    cK
    @6
    vy
    cK
    nfcv
    wps
    vy
    va
    cL
    ovmpt3rab1.y
    vy
    cL
    nfcv
    nfrab
    nfmpt
    ovmpt2dxf
end
