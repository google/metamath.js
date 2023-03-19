include "wceq.mm"
include "wa.mm"
include "wbr.mm"
include "co.mm"
include "clat.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "dalemkelat.mm"
include "dalemseb.mm"
include "dalemtjueb.mm"
include "eqid.mm"
include "latlej1.mm"
include "syl3anc.mm"
include "chlt.mm"
include "dalemkehl.mm"
include "dalemsea.mm"
include "dalemtea.mm"
include "dalemuea.mm"
include "hlatjass.mm"
include "syl13anc.mm"
include "breqtrrd.mm"
include "syl6breqr.mm"
include "adantr.mm"
include "simpr.mm"

theorem dalemsly
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
  assume dalemsly.z: |- Z = ( ( S .\/ T ) .\/ U )


  assert |- ( ( ph /\ Y = Z ) -> S .<_ Y )

  proof
    wph
    cY
    cZ
    wceq
    #
    wa
    cS
    cZ
    cY
    c.le
    wph
    cS
    cZ
    c.le
    wbr
    @0
    wph
    cS
    cS
    cT
    c.or
    co
    cU
    c.or
    co
    #
    cZ
    c.le
    wph
    cS
    cS
    cT
    cU
    c.or
    co
    #
    c.or
    co
    #
    @1
    c.le
    wph
    cK
    clat
    wcel
    cS
    cK
    cbs
    cfv
    #
    wcel
    @2
    @4
    wcel
    cS
    @3
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
    dalemkelat
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
    dalemseb
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
    dalemtjueb
    @4
    c.or
    cK
    c.le
    cS
    @2
    @4
    eqid
    dalemc.l
    dalemc.j
    latlej1
    syl3anc
    wph
    cK
    chlt
    wcel
    cS
    cA
    wcel
    cT
    cA
    wcel
    cU
    cA
    wcel
    @1
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
    dalemsea
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
    cA
    cS
    cT
    cU
    c.or
    cK
    dalemc.j
    dalemc.a
    hlatjass
    syl13anc
    breqtrrd
    dalemsly.z
    syl6breqr
    adantr
    wph
    @0
    simpr
    breqtrrd
end
