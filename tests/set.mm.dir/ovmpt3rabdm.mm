include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "cdm.mm"
include "wsbc.mm"
include "crab.mm"
include "cmpt.mm"
include "wceq.mm"
include "cv.mm"
include "sbceq1a.mm"
include "sylan9bbr.mm"
include "nfsbc1v.mm"
include "nfcv.mm"
include "nfsbc.mm"
include "ovmpt3rab1.mm"
include "adantr.mm"
include "dmeqd.mm"
include "cvv.mm"
include "wral.mm"
include "rabexg.mm"
include "adantl.mm"
include "ralrimivw.mm"
include "dmmptg.mm"
include "syl.mm"
include "eqtrd.mm"

theorem ovmpt3rabdm
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cT: class T
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
  disjoint L z
  disjoint T z
  disjoint U z
  disjoint V z
  disjoint W z
  assert |- ( ( ( X e. V /\ Y e. W /\ K e. U ) /\ L e. T ) -> dom ( X O Y ) = K )

  proof
    cX
    cV
    wcel
    cY
    cW
    wcel
    cK
    cU
    wcel
    w3a
    #
    cL
    cT
    wcel
    #
    wa
    #
    cX
    cY
    cO
    co
    #
    cdm
    vz
    cK
    wph
    vy
    cY
    wsbc
    #
    vx
    cX
    wsbc
    #
    va
    cL
    crab
    #
    cmpt
    #
    cdm
    #
    cK
    @2
    @3
    @7
    @0
    @3
    @7
    wceq
    @1
    wph
    @5
    vx
    vy
    vz
    cU
    cK
    cL
    cM
    cN
    cO
    cV
    cW
    cX
    cY
    va
    ovmpt3rab1.o
    ovmpt3rab1.m
    ovmpt3rab1.n
    vy
    cv
    cY
    wceq
    wph
    @4
    vx
    cv
    cX
    wceq
    @5
    wph
    vy
    cY
    sbceq1a
    @4
    vx
    cX
    sbceq1a
    sylan9bbr
    @4
    vx
    cX
    nfsbc1v
    @4
    vy
    vx
    cX
    vy
    cX
    nfcv
    wph
    vy
    cY
    nfsbc1v
    nfsbc
    ovmpt3rab1
    adantr
    dmeqd
    @2
    @6
    cvv
    wcel
    #
    vz
    cK
    wral
    @8
    cK
    wceq
    @2
    @9
    vz
    cK
    @1
    @9
    @0
    @5
    va
    cL
    cT
    rabexg
    adantl
    ralrimivw
    vz
    cK
    @6
    cvv
    dmmptg
    syl
    eqtrd
end
