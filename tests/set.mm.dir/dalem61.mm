include "wceq.mm"
include "w3a.mm"
include "cv.mm"
include "co.mm"
include "eqid.mm"
include "dalem59.mm"
include "dalem60.mm"
include "breqtrrd.mm"

theorem dalem61
  let wph: wff ph
  let wps: wff ps
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
  assume dalem.ph: |- ( ph <-> ( ( ( K e. HL /\ C e. ( Base ` K ) ) /\ ( P e. A /\ Q e. A /\ R e. A ) /\ ( S e. A /\ T e. A /\ U e. A ) ) /\ ( Y e. O /\ Z e. O ) /\ ( ( -. C .<_ ( P .\/ Q ) /\ -. C .<_ ( Q .\/ R ) /\ -. C .<_ ( R .\/ P ) ) /\ ( -. C .<_ ( S .\/ T ) /\ -. C .<_ ( T .\/ U ) /\ -. C .<_ ( U .\/ S ) ) /\ ( C .<_ ( P .\/ S ) /\ C .<_ ( Q .\/ T ) /\ C .<_ ( R .\/ U ) ) ) ) )
  assume dalem.l: |- .<_ = ( le ` K )
  assume dalem.j: |- .\/ = ( join ` K )
  assume dalem.a: |- A = ( Atoms ` K )
  assume dalem.ps: |- ( ps <-> ( ( c e. A /\ d e. A ) /\ -. c .<_ Y /\ ( d =/= c /\ -. d .<_ Y /\ C .<_ ( c .\/ d ) ) ) )
  assume dalem61.m: |- ./\ = ( meet ` K )
  assume dalem61.o: |- O = ( LPlanes ` K )
  assume dalem61.y: |- Y = ( ( P .\/ Q ) .\/ R )
  assume dalem61.z: |- Z = ( ( S .\/ T ) .\/ U )
  assume dalem61.d: |- D = ( ( P .\/ Q ) ./\ ( S .\/ T ) )
  assume dalem61.e: |- E = ( ( Q .\/ R ) ./\ ( T .\/ U ) )
  assume dalem61.f: |- F = ( ( R .\/ P ) ./\ ( U .\/ S ) )


  assert |- ( ( ph /\ Y = Z /\ ps ) -> F .<_ ( D .\/ E ) )

  proof
    wph
    cY
    cZ
    wceq
    wps
    w3a
    cF
    vc
    cv
    #
    cP
    c.or
    co
    vd
    cv
    #
    cS
    c.or
    co
    c.an
    co
    #
    @0
    cQ
    c.or
    co
    @1
    cT
    c.or
    co
    c.an
    co
    #
    c.or
    co
    @0
    cR
    c.or
    co
    @1
    cU
    c.or
    co
    c.an
    co
    #
    c.or
    co
    cY
    c.an
    co
    #
    cD
    cE
    c.or
    co
    c.le
    wph
    wps
    cA
    @5
    cC
    cP
    cQ
    cR
    cS
    cT
    cU
    cF
    @2
    @3
    @4
    c.or
    cK
    c.le
    c.an
    cO
    cY
    cZ
    vc
    vd
    dalem.ph
    dalem.l
    dalem.j
    dalem.a
    dalem.ps
    dalem61.m
    dalem61.o
    dalem61.y
    dalem61.z
    dalem61.f
    @2
    eqid
    #
    @3
    eqid
    #
    @4
    eqid
    #
    @5
    eqid
    #
    dalem59
    wph
    wps
    cA
    @5
    cC
    cD
    cP
    cQ
    cR
    cS
    cT
    cU
    cE
    @2
    @3
    @4
    c.or
    cK
    c.le
    c.an
    cO
    cY
    cZ
    vc
    vd
    dalem.ph
    dalem.l
    dalem.j
    dalem.a
    dalem.ps
    dalem61.m
    dalem61.o
    dalem61.y
    dalem61.z
    dalem61.d
    dalem61.e
    @6
    @7
    @8
    @9
    dalem60
    breqtrrd
end
