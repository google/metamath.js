include "wceq.mm"
include "wa.mm"
include "co.mm"
include "simpr.mm"
include "dalemqrprot.mm"
include "syl6reqr.mm"
include "adantr.mm"
include "chlt.mm"
include "wcel.mm"
include "dalemkehl.mm"
include "dalemtea.mm"
include "dalemuea.mm"
include "dalemsea.mm"
include "hlatjrot.mm"
include "syl13anc.mm"
include "3eqtr3d.mm"

theorem dalemrotyz
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
  let cY: class Y
  let cZ: class Z
  assume dalema.ph: |- ( ph <-> ( ( ( K e. HL /\ C e. ( Base ` K ) ) /\ ( P e. A /\ Q e. A /\ R e. A ) /\ ( S e. A /\ T e. A /\ U e. A ) ) /\ ( Y e. O /\ Z e. O ) /\ ( ( -. C .<_ ( P .\/ Q ) /\ -. C .<_ ( Q .\/ R ) /\ -. C .<_ ( R .\/ P ) ) /\ ( -. C .<_ ( S .\/ T ) /\ -. C .<_ ( T .\/ U ) /\ -. C .<_ ( U .\/ S ) ) /\ ( C .<_ ( P .\/ S ) /\ C .<_ ( Q .\/ T ) /\ C .<_ ( R .\/ U ) ) ) ) )
  assume dalemc.l: |- .<_ = ( le ` K )
  assume dalemc.j: |- .\/ = ( join ` K )
  assume dalemc.a: |- A = ( Atoms ` K )
  assume dalemrot.y: |- Y = ( ( P .\/ Q ) .\/ R )
  assume dalemrot.z: |- Z = ( ( S .\/ T ) .\/ U )


  assert |- ( ( ph /\ Y = Z ) -> ( ( Q .\/ R ) .\/ P ) = ( ( T .\/ U ) .\/ S ) )

  proof
    wph
    cY
    cZ
    wceq
    #
    wa
    cY
    cZ
    cQ
    cR
    c.or
    co
    cP
    c.or
    co
    #
    cT
    cU
    c.or
    co
    cS
    c.or
    co
    #
    wph
    @0
    simpr
    wph
    cY
    @1
    wceq
    @0
    wph
    @1
    cP
    cQ
    c.or
    co
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
    dalemrot.y
    syl6reqr
    adantr
    wph
    cZ
    @2
    wceq
    @0
    wph
    @2
    cS
    cT
    c.or
    co
    cU
    c.or
    co
    #
    cZ
    wph
    cK
    chlt
    wcel
    cT
    cA
    wcel
    cU
    cA
    wcel
    cS
    cA
    wcel
    @2
    @3
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
    dalemrot.z
    syl6reqr
    adantr
    3eqtr3d
end
