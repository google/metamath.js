include "wceq.mm"
include "w3a.mm"
include "wbr.mm"
include "co.mm"
include "chlt.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "wa.mm"
include "wn.mm"
include "cv.mm"
include "wne.mm"
include "dalemrot.mm"
include "3ad2ant1.mm"
include "dalemrotyz.mm"
include "3adant3.mm"
include "dalemrotps.mm"
include "3adant2.mm"
include "biid.mm"
include "eqid.mm"
include "dalem30.mm"
include "syl3anc.mm"
include "wb.mm"
include "dalemqrprot.mm"
include "syl6reqr.mm"
include "breq2d.mm"
include "mtbird.mm"

theorem dalem35
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
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
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
  assume dalem34.m: |- ./\ = ( meet ` K )
  assume dalem34.o: |- O = ( LPlanes ` K )
  assume dalem34.y: |- Y = ( ( P .\/ Q ) .\/ R )
  assume dalem34.z: |- Z = ( ( S .\/ T ) .\/ U )
  assume dalem34.i: |- I = ( ( c .\/ R ) ./\ ( d .\/ U ) )


  assert |- ( ( ph /\ Y = Z /\ ps ) -> -. I .<_ Y )

  proof
    wph
    cY
    cZ
    wceq
    #
    wps
    w3a
    #
    cI
    cY
    c.le
    wbr
    #
    cI
    cQ
    cR
    c.or
    co
    #
    cP
    c.or
    co
    #
    c.le
    wbr
    #
    @1
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
    @4
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
    @3
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
    @6
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
    @4
    @7
    wceq
    #
    vc
    cv
    #
    cA
    wcel
    vd
    cv
    #
    cA
    wcel
    wa
    @11
    @4
    c.le
    wbr
    wn
    @12
    @11
    wne
    @12
    @4
    c.le
    wbr
    wn
    cC
    @11
    @12
    c.or
    co
    c.le
    wbr
    w3a
    w3a
    #
    @5
    wn
    wph
    @0
    @9
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
    dalem34.y
    dalem34.z
    dalemrot
    3ad2ant1
    wph
    @0
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
    dalem34.y
    dalem34.z
    dalemrotyz
    3adant3
    wph
    wps
    @13
    @0
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
    dalem34.y
    dalemrotps
    3adant2
    @9
    @13
    cA
    cC
    cQ
    cR
    cP
    cT
    cU
    cS
    cI
    c.or
    cK
    c.le
    c.an
    cO
    @4
    @7
    vc
    vd
    @9
    biid
    dalem.l
    dalem.j
    dalem.a
    @13
    biid
    dalem34.m
    dalem34.o
    @4
    eqid
    @7
    eqid
    dalem34.i
    dalem30
    syl3anc
    wph
    @0
    @2
    @5
    wb
    wps
    wph
    cY
    @4
    cI
    c.le
    wph
    @4
    @8
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
    dalem.ph
    dalem.j
    dalem.a
    dalemqrprot
    dalem34.y
    syl6reqr
    breq2d
    3ad2ant1
    mtbird
end
