include "co.mm"
include "chlt.mm"
include "wcel.mm"
include "wceq.mm"
include "dalemkehl.mm"
include "dalempea.mm"
include "dalemqea.mm"
include "dalemsea.mm"
include "dalemtea.mm"
include "hlatj4.mm"
include "syl122anc.mm"
include "cmee.mm"
include "cfv.mm"
include "clln.mm"
include "wne.mm"
include "cp0.mm"
include "dalempjsen.mm"
include "dalemqnet.mm"
include "eqid.mm"
include "llni2.mm"
include "syl31anc.mm"
include "dalem1.mm"
include "wbr.mm"
include "dalemcea.mm"
include "dalemclpjs.mm"
include "dalemclqjt.mm"
include "2llnm4.mm"
include "syl132anc.mm"
include "2llnmat.mm"
include "syl32anc.mm"
include "wb.mm"
include "2llnmj.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "eqeltrd.mm"

theorem dalem2
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
  assume dalem1.o: |- O = ( LPlanes ` K )
  assume dalem1.y: |- Y = ( ( P .\/ Q ) .\/ R )


  assert |- ( ph -> ( ( P .\/ Q ) .\/ ( S .\/ T ) ) e. O )

  proof
    wph
    cP
    cQ
    c.or
    co
    cS
    cT
    c.or
    co
    c.or
    co
    #
    cP
    cS
    c.or
    co
    #
    cQ
    cT
    c.or
    co
    #
    c.or
    co
    #
    cO
    wph
    cK
    chlt
    wcel
    #
    cP
    cA
    wcel
    cQ
    cA
    wcel
    #
    cS
    cA
    wcel
    cT
    cA
    wcel
    #
    @0
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
    dalempea
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
    #
    cA
    cP
    cQ
    cS
    cT
    c.or
    cK
    dalemc.j
    dalemc.a
    hlatj4
    syl122anc
    wph
    @1
    @2
    cK
    cmee
    cfv
    #
    co
    #
    cA
    wcel
    #
    @3
    cO
    wcel
    #
    wph
    @4
    @1
    cK
    clln
    cfv
    #
    wcel
    #
    @2
    @14
    wcel
    #
    @1
    @2
    wne
    @11
    cK
    cp0
    cfv
    #
    wne
    #
    @12
    @7
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
    dalem1.o
    dalem1.y
    dalempjsen
    #
    wph
    @4
    @5
    @6
    cQ
    cT
    wne
    @16
    @7
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
    dalemc.l
    dalemc.j
    dalemc.a
    dalem1.o
    dalem1.y
    dalemqnet
    cA
    cQ
    cT
    c.or
    cK
    @14
    dalemc.j
    dalemc.a
    @14
    eqid
    #
    llni2
    syl31anc
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
    dalem1.o
    dalem1.y
    dalem1
    wph
    @4
    cC
    cA
    wcel
    @15
    @16
    cC
    @1
    c.le
    wbr
    cC
    @2
    c.le
    wbr
    @18
    @7
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
    dalem1.o
    dalem1.y
    dalemcea
    @19
    @21
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
    dalemclpjs
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
    dalemclqjt
    cA
    cC
    cK
    c.le
    @10
    @14
    @1
    @2
    @17
    dalemc.l
    @10
    eqid
    #
    @17
    eqid
    #
    dalemc.a
    @20
    2llnm4
    syl132anc
    cA
    cK
    @10
    @14
    @1
    @2
    @17
    @22
    @23
    dalemc.a
    @20
    2llnmat
    syl32anc
    wph
    @4
    @15
    @16
    @12
    @13
    wb
    @7
    @19
    @21
    cA
    cO
    c.or
    cK
    @10
    @14
    @1
    @2
    dalemc.j
    @22
    dalemc.a
    @20
    dalem1.o
    2llnmj
    syl3anc
    mpbid
    eqeltrd
end
