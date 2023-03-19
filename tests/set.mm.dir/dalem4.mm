include "wne.mm"
include "wa.mm"
include "co.mm"
include "chlt.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "dalemswapyz.mm"
include "adantr.mm"
include "clat.mm"
include "wceq.mm"
include "dalemkelat.mm"
include "dalempjqeb.mm"
include "dalemsjteb.mm"
include "eqid.mm"
include "latmcom.mm"
include "syl3anc.mm"
include "syl5eq.mm"
include "neeq1d.mm"
include "biimpa.mm"
include "biid.mm"
include "dalem3.mm"
include "syl2anc.mm"
include "dalemkehl.mm"
include "dalemqea.mm"
include "dalemrea.mm"
include "hlatjcl.mm"
include "dalemtjueb.mm"
include "3netr4d.mm"

theorem dalem4
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


  assert |- ( ( ph /\ D =/= T ) -> D =/= E )

  proof
    wph
    cD
    cT
    wne
    #
    wa
    #
    cS
    cT
    c.or
    co
    #
    cP
    cQ
    c.or
    co
    #
    c.an
    co
    #
    cT
    cU
    c.or
    co
    #
    cQ
    cR
    c.or
    co
    #
    c.an
    co
    #
    cD
    cE
    @1
    cK
    chlt
    wcel
    #
    cC
    cK
    cbs
    cfv
    #
    wcel
    wa
    cS
    cA
    wcel
    cT
    cA
    wcel
    cU
    cA
    wcel
    w3a
    cP
    cA
    wcel
    cQ
    cA
    wcel
    #
    cR
    cA
    wcel
    #
    w3a
    w3a
    cZ
    cO
    wcel
    cY
    cO
    wcel
    wa
    cC
    @2
    c.le
    wbr
    wn
    cC
    @5
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
    w3a
    cC
    @3
    c.le
    wbr
    wn
    cC
    @6
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
    w3a
    cC
    cS
    cP
    c.or
    co
    c.le
    wbr
    cC
    cT
    cQ
    c.or
    co
    c.le
    wbr
    cC
    cU
    cR
    c.or
    co
    c.le
    wbr
    w3a
    w3a
    w3a
    #
    @4
    cT
    wne
    #
    @4
    @7
    wne
    wph
    @12
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
    dalemswapyz
    adantr
    wph
    @0
    @13
    wph
    cD
    @4
    cT
    wph
    cD
    @3
    @2
    c.an
    co
    #
    @4
    dalem3.d
    wph
    cK
    clat
    wcel
    #
    @3
    @9
    wcel
    @2
    @9
    wcel
    @14
    @4
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
    @9
    cK
    c.an
    @3
    @2
    @9
    eqid
    #
    dalem3.m
    latmcom
    syl3anc
    syl5eq
    #
    neeq1d
    biimpa
    @12
    cA
    cC
    @4
    cS
    cT
    cU
    cP
    cQ
    cR
    @7
    c.or
    cK
    c.le
    c.an
    cO
    cZ
    cY
    @12
    biid
    dalemc.l
    dalemc.j
    dalemc.a
    dalem3.m
    dalem3.o
    dalem3.z
    dalem3.y
    @4
    eqid
    @7
    eqid
    dalem3
    syl2anc
    wph
    cD
    @4
    wceq
    @0
    @18
    adantr
    wph
    cE
    @7
    wceq
    @0
    wph
    cE
    @6
    @5
    c.an
    co
    #
    @7
    dalem3.e
    wph
    @15
    @6
    @9
    wcel
    #
    @5
    @9
    wcel
    @19
    @7
    wceq
    @16
    wph
    @8
    @10
    @11
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
    dalemqea
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
    cA
    @9
    c.or
    cK
    cQ
    cR
    @17
    dalemc.j
    dalemc.a
    hlatjcl
    syl3anc
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
    @9
    cK
    c.an
    @6
    @5
    @17
    dalem3.m
    latmcom
    syl3anc
    syl5eq
    adantr
    3netr4d
end
