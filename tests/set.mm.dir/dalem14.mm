include "wne.mm"
include "wa.mm"
include "co.mm"
include "dalem13.mm"
include "dalem9.mm"
include "eqeltrd.mm"

theorem dalem14
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
  assume dalem14.o: |- O = ( LPlanes ` K )
  assume dalem14.v: |- V = ( LVols ` K )
  assume dalem14.y: |- Y = ( ( P .\/ Q ) .\/ R )
  assume dalem14.z: |- Z = ( ( S .\/ T ) .\/ U )
  assume dalem14.w: |- W = ( Y .\/ C )


  assert |- ( ( ph /\ Y =/= Z ) -> ( Y .\/ Z ) e. V )

  proof
    wph
    cY
    cZ
    wne
    wa
    cY
    cZ
    c.or
    co
    cW
    cV
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
    cW
    cY
    cZ
    dalema.ph
    dalemc.l
    dalemc.j
    dalemc.a
    dalem14.o
    dalem14.y
    dalem14.z
    dalem14.w
    dalem13
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
    cV
    cW
    cY
    cZ
    dalema.ph
    dalemc.l
    dalemc.j
    dalemc.a
    dalem14.o
    dalem14.v
    dalem14.y
    dalem14.z
    dalem14.w
    dalem9
    eqeltrd
end
