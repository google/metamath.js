include "co.mm"
include "chlt.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "wa.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "dalemrot.mm"
include "biid.mm"
include "eqid.mm"
include "dalem10.mm"
include "syl.mm"
include "dalemqrprot.mm"
include "syl6reqr.mm"
include "wceq.mm"
include "dalemkehl.mm"
include "dalemtea.mm"
include "dalemuea.mm"
include "dalemsea.mm"
include "hlatjrot.mm"
include "syl13anc.mm"
include "oveq12d.mm"
include "syl5eq.mm"
include "breqtrrd.mm"

theorem dalem11
  let wph: wff ph
  let cA: class A
  let cC: class C
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
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume dalema.ph: |- ( ph <-> ( ( ( K e. HL /\ C e. ( Base ` K ) ) /\ ( P e. A /\ Q e. A /\ R e. A ) /\ ( S e. A /\ T e. A /\ U e. A ) ) /\ ( Y e. O /\ Z e. O ) /\ ( ( -. C .<_ ( P .\/ Q ) /\ -. C .<_ ( Q .\/ R ) /\ -. C .<_ ( R .\/ P ) ) /\ ( -. C .<_ ( S .\/ T ) /\ -. C .<_ ( T .\/ U ) /\ -. C .<_ ( U .\/ S ) ) /\ ( C .<_ ( P .\/ S ) /\ C .<_ ( Q .\/ T ) /\ C .<_ ( R .\/ U ) ) ) ) )
  assume dalemc.l: |- .<_ = ( le ` K )
  assume dalemc.j: |- .\/ = ( join ` K )
  assume dalemc.a: |- A = ( Atoms ` K )
  assume dalem11.m: |- ./\ = ( meet ` K )
  assume dalem11.o: |- O = ( LPlanes ` K )
  assume dalem11.y: |- Y = ( ( P .\/ Q ) .\/ R )
  assume dalem11.z: |- Z = ( ( S .\/ T ) .\/ U )
  assume dalem11.x: |- X = ( Y ./\ Z )
  assume dalem11.e: |- E = ( ( Q .\/ R ) ./\ ( T .\/ U ) )


  assert |- ( ph -> E .<_ X )

  proof
    wph
    cE
    cQ
    cR
    c.or
    co
    #
    cP
    c.or
    co
    #
    cT
    cU
    c.or
    co
    #
    cS
    c.or
    co
    #
    c.an
    co
    #
    cX
    c.le
    wph
    cK
    chlt
    wcel
    #
    cC
    cK
    cbs
    cfv
    wcel
    wa
    cQ
    cA
    wcel
    cR
    cA
    wcel
    cP
    cA
    wcel
    w3a
    cT
    cA
    wcel
    #
    cU
    cA
    wcel
    #
    cS
    cA
    wcel
    #
    w3a
    w3a
    @1
    cO
    wcel
    @3
    cO
    wcel
    wa
    cC
    @0
    c.le
    wbr
    wn
    cC
    cR
    cP
    c.or
    co
    c.le
    wbr
    wn
    cC
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    wn
    w3a
    cC
    @2
    c.le
    wbr
    wn
    cC
    cU
    cS
    c.or
    co
    c.le
    wbr
    wn
    cC
    cS
    cT
    c.or
    co
    #
    c.le
    wbr
    wn
    w3a
    cC
    cQ
    cT
    c.or
    co
    c.le
    wbr
    cC
    cR
    cU
    c.or
    co
    c.le
    wbr
    cC
    cP
    cS
    c.or
    co
    c.le
    wbr
    w3a
    w3a
    w3a
    #
    cE
    @4
    c.le
    wbr
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
    dalem11.y
    dalem11.z
    dalemrot
    @11
    cA
    cC
    cE
    cQ
    cR
    cP
    cT
    cU
    cS
    c.or
    cK
    c.le
    c.an
    cO
    @4
    @1
    @3
    @11
    biid
    dalemc.l
    dalemc.j
    dalemc.a
    dalem11.m
    dalem11.o
    @1
    eqid
    @3
    eqid
    @4
    eqid
    dalem11.e
    dalem10
    syl
    wph
    cX
    cY
    cZ
    c.an
    co
    @4
    dalem11.x
    wph
    cY
    @1
    cZ
    @3
    c.an
    wph
    @1
    @9
    cR
    c.or
    co
    cY
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
    dalemqrprot
    dalem11.y
    syl6reqr
    wph
    @3
    @10
    cU
    c.or
    co
    #
    cZ
    wph
    @5
    @6
    @7
    @8
    @3
    @12
    wceq
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
    dalemtea
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
    dalemsea
    cA
    cT
    cU
    cS
    c.or
    cK
    dalemc.j
    dalemc.a
    hlatjrot
    syl13anc
    dalem11.z
    syl6reqr
    oveq12d
    syl5eq
    breqtrrd
end
