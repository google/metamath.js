include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "wcel.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "co.mm"
include "w3a.mm"
include "wex.mm"
include "biid.mm"
include "dalem20.mm"
include "dalem61.mm"
include "3expia.mm"
include "exlimdvv.mm"
include "mpd.mm"

theorem dalem62
  let wph: wff ph
  let cA: class A
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cE: class E
  let cF: class F
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cO: class O
  let cY: class Y
  let cZ: class Z
  let vc: setvar c
  let vd: setvar d
  assume dalem62.ph: |- ( ph <-> ( ( ( K e. HL /\ C e. ( Base ` K ) ) /\ ( P e. A /\ Q e. A /\ R e. A ) /\ ( S e. A /\ T e. A /\ U e. A ) ) /\ ( Y e. O /\ Z e. O ) /\ ( ( -. C .<_ ( P .\/ Q ) /\ -. C .<_ ( Q .\/ R ) /\ -. C .<_ ( R .\/ P ) ) /\ ( -. C .<_ ( S .\/ T ) /\ -. C .<_ ( T .\/ U ) /\ -. C .<_ ( U .\/ S ) ) /\ ( C .<_ ( P .\/ S ) /\ C .<_ ( Q .\/ T ) /\ C .<_ ( R .\/ U ) ) ) ) )
  assume dalem62.l: |- .<_ = ( le ` K )
  assume dalem62.j: |- .\/ = ( join ` K )
  assume dalem62.a: |- A = ( Atoms ` K )
  assume dalem62.m: |- ./\ = ( meet ` K )
  assume dalem62.o: |- O = ( LPlanes ` K )
  assume dalem62.y: |- Y = ( ( P .\/ Q ) .\/ R )
  assume dalem62.z: |- Z = ( ( S .\/ T ) .\/ U )
  assume dalem62.d: |- D = ( ( P .\/ Q ) ./\ ( S .\/ T ) )
  assume dalem62.e: |- E = ( ( Q .\/ R ) ./\ ( T .\/ U ) )
  assume dalem62.f: |- F = ( ( R .\/ P ) ./\ ( U .\/ S ) )


  assert |- ( ( ph /\ Y = Z ) -> F .<_ ( D .\/ E ) )

  proof
    wph
    cY
    cZ
    wceq
    #
    wa
    #
    vc
    cv
    #
    cA
    wcel
    vd
    cv
    #
    cA
    wcel
    wa
    @2
    cY
    c.le
    wbr
    wn
    @3
    @2
    wne
    @3
    cY
    c.le
    wbr
    wn
    cC
    @2
    @3
    c.or
    co
    c.le
    wbr
    w3a
    w3a
    #
    vd
    wex
    vc
    wex
    cF
    cD
    cE
    c.or
    co
    c.le
    wbr
    #
    wph
    @4
    cA
    cC
    cP
    cQ
    cR
    cS
    cT
    cU
    c.or
    cK
    c.le
    cO
    cY
    cZ
    vc
    vd
    dalem62.ph
    dalem62.l
    dalem62.j
    dalem62.a
    @4
    biid
    #
    dalem62.o
    dalem62.y
    dalem62.z
    dalem20
    @1
    @4
    @5
    vc
    vd
    wph
    @0
    @4
    @5
    wph
    @4
    cA
    cC
    cD
    cP
    cQ
    cR
    cS
    cT
    cU
    cE
    cF
    c.or
    cK
    c.le
    c.an
    cO
    cY
    cZ
    vc
    vd
    dalem62.ph
    dalem62.l
    dalem62.j
    dalem62.a
    @6
    dalem62.m
    dalem62.o
    dalem62.y
    dalem62.z
    dalem62.d
    dalem62.e
    dalem62.f
    dalem61
    3expia
    exlimdvv
    mpd
end
