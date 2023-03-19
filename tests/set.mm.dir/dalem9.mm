include "wne.mm"
include "wa.mm"
include "co.mm"
include "chlt.mm"
include "wcel.mm"
include "wbr.mm"
include "wn.mm"
include "dalemkehl.mm"
include "adantr.mm"
include "dalemyeo.mm"
include "dalemcea.mm"
include "dalem-cly.mm"
include "lvoli3.mm"
include "syl31anc.mm"
include "syl5eqel.mm"

theorem dalem9
  let wph: wff ph
  let cA: class A
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cO: class O
  let cV: class V
  let cW: class W
  let cY: class Y
  let cZ: class Z
  assume dalema.ph: |- ( ph <-> ( ( ( K e. HL /\ C e. ( Base ` K ) ) /\ ( P e. A /\ Q e. A /\ R e. A ) /\ ( S e. A /\ T e. A /\ U e. A ) ) /\ ( Y e. O /\ Z e. O ) /\ ( ( -. C .<_ ( P .\/ Q ) /\ -. C .<_ ( Q .\/ R ) /\ -. C .<_ ( R .\/ P ) ) /\ ( -. C .<_ ( S .\/ T ) /\ -. C .<_ ( T .\/ U ) /\ -. C .<_ ( U .\/ S ) ) /\ ( C .<_ ( P .\/ S ) /\ C .<_ ( Q .\/ T ) /\ C .<_ ( R .\/ U ) ) ) ) )
  assume dalemc.l: |- .<_ = ( le ` K )
  assume dalemc.j: |- .\/ = ( join ` K )
  assume dalemc.a: |- A = ( Atoms ` K )
  assume dalem9.o: |- O = ( LPlanes ` K )
  assume dalem9.v: |- V = ( LVols ` K )
  assume dalem9.y: |- Y = ( ( P .\/ Q ) .\/ R )
  assume dalem9.z: |- Z = ( ( S .\/ T ) .\/ U )
  assume dalem9.w: |- W = ( Y .\/ C )


  assert |- ( ( ph /\ Y =/= Z ) -> W e. V )

  proof
    wph
    cY
    cZ
    wne
    #
    wa
    #
    cW
    cY
    cC
    c.or
    co
    #
    cV
    dalem9.w
    @1
    cK
    chlt
    wcel
    #
    cY
    cO
    wcel
    #
    cC
    cA
    wcel
    #
    cC
    cY
    c.le
    wbr
    wn
    @2
    cV
    wcel
    wph
    @3
    @0
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
    adantr
    wph
    @4
    @0
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
    adantr
    wph
    @5
    @0
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
    dalem9.o
    dalem9.y
    dalemcea
    adantr
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
    dalem9.o
    dalem9.y
    dalem9.z
    dalem-cly
    cA
    cO
    cC
    c.or
    cK
    c.le
    cV
    cY
    dalemc.l
    dalemc.j
    dalemc.a
    dalem9.o
    dalem9.v
    lvoli3
    syl31anc
    syl5eqel
end
