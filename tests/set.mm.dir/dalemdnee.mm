include "wne.mm"
include "wceq.mm"
include "wa.mm"
include "simpr.mm"
include "dalemqnet.mm"
include "adantr.mm"
include "eqnetrd.mm"
include "dalem4.mm"
include "syldan.mm"
include "dalem3.mm"
include "pm2.61dane.mm"

theorem dalemdnee
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
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cO: class O
  let cY: class Y
  let cZ: class Z
  assume dalema.ph: |- ( ph <-> ( ( ( K e. HL /\ C e. ( Base ` K ) ) /\ ( P e. A /\ Q e. A /\ R e. A ) /\ ( S e. A /\ T e. A /\ U e. A ) ) /\ ( Y e. O /\ Z e. O ) /\ ( ( -. C .<_ ( P .\/ Q ) /\ -. C .<_ ( Q .\/ R ) /\ -. C .<_ ( R .\/ P ) ) /\ ( -. C .<_ ( S .\/ T ) /\ -. C .<_ ( T .\/ U ) /\ -. C .<_ ( U .\/ S ) ) /\ ( C .<_ ( P .\/ S ) /\ C .<_ ( Q .\/ T ) /\ C .<_ ( R .\/ U ) ) ) ) )
  assume dalemc.l: |- .<_ = ( le ` K )
  assume dalemc.j: |- .\/ = ( join ` K )
  assume dalemc.a: |- A = ( Atoms ` K )
  assume dalem3.m: |- ./\ = ( meet ` K )
  assume dalem3.o: |- O = ( LPlanes ` K )
  assume dalem3.y: |- Y = ( ( P .\/ Q ) .\/ R )
  assume dalem3.z: |- Z = ( ( S .\/ T ) .\/ U )
  assume dalem3.d: |- D = ( ( P .\/ Q ) ./\ ( S .\/ T ) )
  assume dalem3.e: |- E = ( ( Q .\/ R ) ./\ ( T .\/ U ) )


  assert |- ( ph -> D =/= E )

  proof
    wph
    cD
    cE
    wne
    #
    cD
    cQ
    wph
    cD
    cQ
    wceq
    #
    cD
    cT
    wne
    @0
    wph
    @1
    wa
    cD
    cQ
    cT
    wph
    @1
    simpr
    wph
    cQ
    cT
    wne
    @1
    wph
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
    dalema.ph
    dalemc.l
    dalemc.j
    dalemc.a
    dalem3.o
    dalem3.y
    dalemqnet
    adantr
    eqnetrd
    wph
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
    c.or
    cK
    c.le
    c.an
    cO
    cY
    cZ
    dalema.ph
    dalemc.l
    dalemc.j
    dalemc.a
    dalem3.m
    dalem3.o
    dalem3.y
    dalem3.z
    dalem3.d
    dalem3.e
    dalem4
    syldan
    wph
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
    c.or
    cK
    c.le
    c.an
    cO
    cY
    cZ
    dalema.ph
    dalemc.l
    dalemc.j
    dalemc.a
    dalem3.m
    dalem3.o
    dalem3.y
    dalem3.z
    dalem3.d
    dalem3.e
    dalem3
    pm2.61dane
end
