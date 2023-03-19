include "wne.mm"
include "wa.mm"
include "co.mm"
include "wcel.mm"
include "clvol.mm"
include "cfv.mm"
include "eqid.mm"
include "dalem14.mm"
include "wb.mm"
include "chlt.mm"
include "dalemkehl.mm"
include "dalemyeo.mm"
include "dalemzeo.mm"
include "2lplnmj.mm"
include "syl3anc.mm"
include "adantr.mm"
include "mpbird.mm"
include "syl5eqel.mm"

theorem dalem15
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
  let c.an: class ./\
  let cN: class N
  let cO: class O
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume dalema.ph: |- ( ph <-> ( ( ( K e. HL /\ C e. ( Base ` K ) ) /\ ( P e. A /\ Q e. A /\ R e. A ) /\ ( S e. A /\ T e. A /\ U e. A ) ) /\ ( Y e. O /\ Z e. O ) /\ ( ( -. C .<_ ( P .\/ Q ) /\ -. C .<_ ( Q .\/ R ) /\ -. C .<_ ( R .\/ P ) ) /\ ( -. C .<_ ( S .\/ T ) /\ -. C .<_ ( T .\/ U ) /\ -. C .<_ ( U .\/ S ) ) /\ ( C .<_ ( P .\/ S ) /\ C .<_ ( Q .\/ T ) /\ C .<_ ( R .\/ U ) ) ) ) )
  assume dalemc.l: |- .<_ = ( le ` K )
  assume dalemc.j: |- .\/ = ( join ` K )
  assume dalemc.a: |- A = ( Atoms ` K )
  assume dalem15.m: |- ./\ = ( meet ` K )
  assume dalem15.n: |- N = ( LLines ` K )
  assume dalem15.o: |- O = ( LPlanes ` K )
  assume dalem15.y: |- Y = ( ( P .\/ Q ) .\/ R )
  assume dalem15.z: |- Z = ( ( S .\/ T ) .\/ U )
  assume dalem15.x: |- X = ( Y ./\ Z )


  assert |- ( ( ph /\ Y =/= Z ) -> X e. N )

  proof
    wph
    cY
    cZ
    wne
    #
    wa
    #
    cX
    cY
    cZ
    c.an
    co
    #
    cN
    dalem15.x
    @1
    @2
    cN
    wcel
    #
    cY
    cZ
    c.or
    co
    cK
    clvol
    cfv
    #
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
    @4
    cY
    cC
    c.or
    co
    #
    cY
    cZ
    dalema.ph
    dalemc.l
    dalemc.j
    dalemc.a
    dalem15.o
    @4
    eqid
    #
    dalem15.y
    dalem15.z
    @6
    eqid
    dalem14
    wph
    @3
    @5
    wb
    #
    @0
    wph
    cK
    chlt
    wcel
    cY
    cO
    wcel
    cZ
    cO
    wcel
    @8
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
    cO
    c.or
    cK
    c.an
    cN
    @4
    cY
    cZ
    dalemc.j
    dalem15.m
    dalem15.n
    dalem15.o
    @7
    2lplnmj
    syl3anc
    adantr
    mpbird
    syl5eqel
end
