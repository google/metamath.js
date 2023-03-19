include "wceq.mm"
include "w3a.mm"
include "cv.mm"
include "co.mm"
include "cmee.mm"
include "cfv.mm"
include "wcel.mm"
include "eqid.mm"
include "dalem21.mm"
include "wb.mm"
include "wa.mm"
include "chlt.mm"
include "clln.mm"
include "dalemkehl.mm"
include "adantr.mm"
include "dalemcjden.mm"
include "dalempjsen.mm"
include "2llnmj.mm"
include "syl3anc.mm"
include "3adant2.mm"
include "mpbid.mm"

theorem dalem22
  let wph: wff ph
  let wps: wff ps
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
  let vc: setvar c
  let vd: setvar d
  assume dalem.ph: |- ( ph <-> ( ( ( K e. HL /\ C e. ( Base ` K ) ) /\ ( P e. A /\ Q e. A /\ R e. A ) /\ ( S e. A /\ T e. A /\ U e. A ) ) /\ ( Y e. O /\ Z e. O ) /\ ( ( -. C .<_ ( P .\/ Q ) /\ -. C .<_ ( Q .\/ R ) /\ -. C .<_ ( R .\/ P ) ) /\ ( -. C .<_ ( S .\/ T ) /\ -. C .<_ ( T .\/ U ) /\ -. C .<_ ( U .\/ S ) ) /\ ( C .<_ ( P .\/ S ) /\ C .<_ ( Q .\/ T ) /\ C .<_ ( R .\/ U ) ) ) ) )
  assume dalem.l: |- .<_ = ( le ` K )
  assume dalem.j: |- .\/ = ( join ` K )
  assume dalem.a: |- A = ( Atoms ` K )
  assume dalem.ps: |- ( ps <-> ( ( c e. A /\ d e. A ) /\ -. c .<_ Y /\ ( d =/= c /\ -. d .<_ Y /\ C .<_ ( c .\/ d ) ) ) )
  assume dalem22.o: |- O = ( LPlanes ` K )
  assume dalem22.y: |- Y = ( ( P .\/ Q ) .\/ R )
  assume dalem22.z: |- Z = ( ( S .\/ T ) .\/ U )


  assert |- ( ( ph /\ Y = Z /\ ps ) -> ( ( c .\/ d ) .\/ ( P .\/ S ) ) e. O )

  proof
    wph
    cY
    cZ
    wceq
    #
    wps
    w3a
    vc
    cv
    vd
    cv
    c.or
    co
    #
    cP
    cS
    c.or
    co
    #
    cK
    cmee
    cfv
    #
    co
    cA
    wcel
    #
    @1
    @2
    c.or
    co
    cO
    wcel
    #
    wph
    wps
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
    @3
    cO
    cY
    cZ
    vc
    vd
    dalem.ph
    dalem.l
    dalem.j
    dalem.a
    dalem.ps
    @3
    eqid
    #
    dalem22.o
    dalem22.y
    dalem22.z
    dalem21
    wph
    wps
    @4
    @5
    wb
    #
    @0
    wph
    wps
    wa
    cK
    chlt
    wcel
    #
    @1
    cK
    clln
    cfv
    #
    wcel
    @2
    @9
    wcel
    #
    @7
    wph
    @8
    wps
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
    dalem.ph
    dalemkehl
    adantr
    wph
    wps
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
    vc
    vd
    dalem.ph
    dalem.l
    dalem.j
    dalem.a
    dalem.ps
    dalemcjden
    wph
    @10
    wps
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
    dalem.ph
    dalem.l
    dalem.j
    dalem.a
    dalem22.o
    dalem22.y
    dalempjsen
    adantr
    cA
    cO
    c.or
    cK
    @3
    @9
    @1
    @2
    dalem.j
    @6
    dalem.a
    @9
    eqid
    dalem22.o
    2llnmj
    syl3anc
    3adant2
    mpbid
end
