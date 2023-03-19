include "co.mm"
include "wcel.mm"
include "dalem2.mm"
include "chlt.mm"
include "clln.mm"
include "cfv.mm"
include "wb.mm"
include "dalemkehl.mm"
include "wne.mm"
include "dalempea.mm"
include "dalemqea.mm"
include "dalemrea.mm"
include "dalemyeo.mm"
include "lplnri1.mm"
include "syl131anc.mm"
include "eqid.mm"
include "llni2.mm"
include "syl31anc.mm"
include "dalemsea.mm"
include "dalemtea.mm"
include "dalemuea.mm"
include "dalemzeo.mm"
include "2llnmj.mm"
include "syl3anc.mm"
include "mpbird.mm"
include "syl5eqel.mm"

theorem dalemdea
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
  assume dalemdea.m: |- ./\ = ( meet ` K )
  assume dalemdea.o: |- O = ( LPlanes ` K )
  assume dalemdea.y: |- Y = ( ( P .\/ Q ) .\/ R )
  assume dalemdea.z: |- Z = ( ( S .\/ T ) .\/ U )
  assume dalemdea.d: |- D = ( ( P .\/ Q ) ./\ ( S .\/ T ) )


  assert |- ( ph -> D e. A )

  proof
    wph
    cD
    cP
    cQ
    c.or
    co
    #
    cS
    cT
    c.or
    co
    #
    c.an
    co
    #
    cA
    dalemdea.d
    wph
    @2
    cA
    wcel
    #
    @0
    @1
    c.or
    co
    cO
    wcel
    #
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
    dalemdea.o
    dalemdea.y
    dalem2
    wph
    cK
    chlt
    wcel
    #
    @0
    cK
    clln
    cfv
    #
    wcel
    #
    @1
    @6
    wcel
    #
    @3
    @4
    wb
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
    dalemkehl
    #
    wph
    @5
    cP
    cA
    wcel
    #
    cQ
    cA
    wcel
    #
    cP
    cQ
    wne
    #
    @7
    @9
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
    dalempea
    #
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
    dalemqea
    #
    wph
    @5
    @10
    @11
    cR
    cA
    wcel
    cY
    cO
    wcel
    @12
    @9
    @13
    @14
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
    dalemrea
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
    dalemyeo
    cA
    cO
    cP
    cQ
    cR
    c.or
    cK
    cY
    dalemc.j
    dalemc.a
    dalemdea.o
    dalemdea.y
    lplnri1
    syl131anc
    cA
    cP
    cQ
    c.or
    cK
    @6
    dalemc.j
    dalemc.a
    @6
    eqid
    #
    llni2
    syl31anc
    wph
    @5
    cS
    cA
    wcel
    #
    cT
    cA
    wcel
    #
    cS
    cT
    wne
    #
    @8
    @9
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
    dalemsea
    #
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
    dalemtea
    #
    wph
    @5
    @16
    @17
    cU
    cA
    wcel
    cZ
    cO
    wcel
    @18
    @9
    @19
    @20
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
    dalemuea
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
    dalemzeo
    cA
    cO
    cS
    cT
    cU
    c.or
    cK
    cZ
    dalemc.j
    dalemc.a
    dalemdea.o
    dalemdea.z
    lplnri1
    syl131anc
    cA
    cS
    cT
    c.or
    cK
    @6
    dalemc.j
    dalemc.a
    @15
    llni2
    syl31anc
    cA
    cO
    c.or
    cK
    c.an
    @6
    @0
    @1
    dalemc.j
    dalemdea.m
    dalemc.a
    @15
    dalemdea.o
    2llnmj
    syl3anc
    mpbird
    syl5eqel
end
