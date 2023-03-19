include "co.mm"
include "wbr.mm"
include "clat.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "dalemkelat.mm"
include "dalempjqeb.mm"
include "dalemreb.mm"
include "eqid.mm"
include "latlej1.mm"
include "syl3anc.mm"
include "dalemsjteb.mm"
include "dalemueb.mm"
include "wa.mm"
include "wi.mm"
include "dalemyeb.mm"
include "syl5eqelr.mm"
include "dalemzeo.mm"
include "lplnbase.mm"
include "syl.mm"
include "latmlem12.mm"
include "syl122anc.mm"
include "mp2and.mm"
include "oveq12i.mm"
include "eqtri.mm"
include "3brtr4g.mm"

theorem dalem10
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
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume dalema.ph: |- ( ph <-> ( ( ( K e. HL /\ C e. ( Base ` K ) ) /\ ( P e. A /\ Q e. A /\ R e. A ) /\ ( S e. A /\ T e. A /\ U e. A ) ) /\ ( Y e. O /\ Z e. O ) /\ ( ( -. C .<_ ( P .\/ Q ) /\ -. C .<_ ( Q .\/ R ) /\ -. C .<_ ( R .\/ P ) ) /\ ( -. C .<_ ( S .\/ T ) /\ -. C .<_ ( T .\/ U ) /\ -. C .<_ ( U .\/ S ) ) /\ ( C .<_ ( P .\/ S ) /\ C .<_ ( Q .\/ T ) /\ C .<_ ( R .\/ U ) ) ) ) )
  assume dalemc.l: |- .<_ = ( le ` K )
  assume dalemc.j: |- .\/ = ( join ` K )
  assume dalemc.a: |- A = ( Atoms ` K )
  assume dalem10.m: |- ./\ = ( meet ` K )
  assume dalem10.o: |- O = ( LPlanes ` K )
  assume dalem10.y: |- Y = ( ( P .\/ Q ) .\/ R )
  assume dalem10.z: |- Z = ( ( S .\/ T ) .\/ U )
  assume dalem10.x: |- X = ( Y ./\ Z )
  assume dalem10.d: |- D = ( ( P .\/ Q ) ./\ ( S .\/ T ) )


  assert |- ( ph -> D .<_ X )

  proof
    wph
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
    @0
    cR
    c.or
    co
    #
    @1
    cU
    c.or
    co
    #
    c.an
    co
    #
    cD
    cX
    c.le
    wph
    @0
    @3
    c.le
    wbr
    #
    @1
    @4
    c.le
    wbr
    #
    @2
    @5
    c.le
    wbr
    #
    wph
    cK
    clat
    wcel
    #
    @0
    cK
    cbs
    cfv
    #
    wcel
    #
    cR
    @10
    wcel
    @6
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
    dalemkelat
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
    dalemc.j
    dalemc.a
    dalempjqeb
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
    dalemc.a
    dalemreb
    @10
    c.or
    cK
    c.le
    @0
    cR
    @10
    eqid
    #
    dalemc.l
    dalemc.j
    latlej1
    syl3anc
    wph
    @9
    @1
    @10
    wcel
    #
    cU
    @10
    wcel
    @7
    @12
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
    dalemc.j
    dalemc.a
    dalemsjteb
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
    dalemc.a
    dalemueb
    @10
    c.or
    cK
    c.le
    @1
    cU
    @14
    dalemc.l
    dalemc.j
    latlej1
    syl3anc
    wph
    @9
    @11
    @3
    @10
    wcel
    @15
    @4
    @10
    wcel
    @6
    @7
    wa
    @8
    wi
    @12
    @13
    wph
    @3
    cY
    @10
    dalem10.y
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
    dalem10.o
    dalemyeb
    syl5eqelr
    @16
    wph
    @4
    cZ
    @10
    dalem10.z
    wph
    cZ
    cO
    wcel
    cZ
    @10
    wcel
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
    @10
    cO
    cK
    cZ
    @14
    dalem10.o
    lplnbase
    syl
    syl5eqelr
    @10
    cK
    c.le
    c.an
    @4
    @0
    @3
    @1
    @14
    dalemc.l
    dalem10.m
    latmlem12
    syl122anc
    mp2and
    dalem10.d
    cX
    cY
    cZ
    c.an
    co
    @5
    dalem10.x
    cY
    @3
    cZ
    @4
    c.an
    dalem10.y
    dalem10.z
    oveq12i
    eqtri
    3brtr4g
end
