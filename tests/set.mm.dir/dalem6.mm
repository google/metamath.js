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
include "dalem5.mm"
include "syl.mm"
include "dalemqrprot.mm"
include "syl6reqr.mm"
include "oveq1d.mm"
include "syl5eq.mm"
include "breqtrrd.mm"

theorem dalem6
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
  let cW: class W
  let cY: class Y
  let cZ: class Z
  assume dalema.ph: |- ( ph <-> ( ( ( K e. HL /\ C e. ( Base ` K ) ) /\ ( P e. A /\ Q e. A /\ R e. A ) /\ ( S e. A /\ T e. A /\ U e. A ) ) /\ ( Y e. O /\ Z e. O ) /\ ( ( -. C .<_ ( P .\/ Q ) /\ -. C .<_ ( Q .\/ R ) /\ -. C .<_ ( R .\/ P ) ) /\ ( -. C .<_ ( S .\/ T ) /\ -. C .<_ ( T .\/ U ) /\ -. C .<_ ( U .\/ S ) ) /\ ( C .<_ ( P .\/ S ) /\ C .<_ ( Q .\/ T ) /\ C .<_ ( R .\/ U ) ) ) ) )
  assume dalemc.l: |- .<_ = ( le ` K )
  assume dalemc.j: |- .\/ = ( join ` K )
  assume dalemc.a: |- A = ( Atoms ` K )
  assume dalem6.o: |- O = ( LPlanes ` K )
  assume dalem6.y: |- Y = ( ( P .\/ Q ) .\/ R )
  assume dalem6.z: |- Z = ( ( S .\/ T ) .\/ U )
  assume dalem6.w: |- W = ( Y .\/ C )


  assert |- ( ph -> S .<_ W )

  proof
    wph
    cS
    cQ
    cR
    c.or
    co
    #
    cP
    c.or
    co
    #
    cC
    c.or
    co
    #
    cW
    c.le
    wph
    cK
    chlt
    wcel
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
    cU
    cA
    wcel
    cS
    cA
    wcel
    w3a
    w3a
    @1
    cO
    wcel
    cT
    cU
    c.or
    co
    #
    cS
    c.or
    co
    #
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
    @3
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
    cS
    @2
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
    dalem6.y
    dalem6.z
    dalemrot
    @6
    cA
    cC
    cQ
    cR
    cP
    cT
    cU
    cS
    c.or
    cK
    c.le
    cO
    @2
    @1
    @4
    @6
    biid
    dalemc.l
    dalemc.j
    dalemc.a
    dalem6.o
    @1
    eqid
    @2
    eqid
    dalem5
    syl
    wph
    cW
    cY
    cC
    c.or
    co
    @2
    dalem6.w
    wph
    cY
    @1
    cC
    c.or
    wph
    @1
    @5
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
    dalem6.y
    syl6reqr
    oveq1d
    syl5eq
    breqtrrd
end
