include "wceq.mm"
include "w3a.mm"
include "co.mm"
include "chlt.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "wa.mm"
include "wbr.mm"
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
include "dalem57.mm"
include "syl3anc.mm"
include "dalemkehl.mm"
include "dalem29.mm"
include "dalem34.mm"
include "dalem23.mm"
include "hlatjrot.mm"
include "syl13anc.mm"
include "dalemqrprot.mm"
include "syl6eqr.mm"
include "oveq12d.mm"
include "breqtrd.mm"

theorem dalem58
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cE: class E
  let cG: class G
  let cH: class H
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
  assume dalem58.m: |- ./\ = ( meet ` K )
  assume dalem58.o: |- O = ( LPlanes ` K )
  assume dalem58.y: |- Y = ( ( P .\/ Q ) .\/ R )
  assume dalem58.z: |- Z = ( ( S .\/ T ) .\/ U )
  assume dalem58.e: |- E = ( ( Q .\/ R ) ./\ ( T .\/ U ) )
  assume dalem58.g: |- G = ( ( c .\/ P ) ./\ ( d .\/ S ) )
  assume dalem58.h: |- H = ( ( c .\/ Q ) ./\ ( d .\/ T ) )
  assume dalem58.i: |- I = ( ( c .\/ R ) ./\ ( d .\/ U ) )
  assume dalem58.b1: |- B = ( ( ( G .\/ H ) .\/ I ) ./\ Y )


  assert |- ( ( ph /\ Y = Z /\ ps ) -> E .<_ B )

  proof
    wph
    cY
    cZ
    wceq
    #
    wps
    w3a
    #
    cE
    cH
    cI
    c.or
    co
    cG
    c.or
    co
    #
    cQ
    cR
    c.or
    co
    #
    cP
    c.or
    co
    #
    c.an
    co
    #
    cB
    c.le
    @1
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
    @7
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
    @8
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
    @12
    @4
    c.le
    wbr
    wn
    @13
    @12
    wne
    @13
    @4
    c.le
    wbr
    wn
    cC
    @12
    @13
    c.or
    co
    c.le
    wbr
    w3a
    w3a
    #
    cE
    @5
    c.le
    wbr
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
    dalem58.y
    dalem58.z
    dalemrot
    3ad2ant1
    wph
    @0
    @11
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
    dalem58.y
    dalem58.z
    dalemrotyz
    3adant3
    wph
    wps
    @14
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
    dalem58.y
    dalemrotps
    3adant2
    @10
    @14
    cA
    @5
    cC
    cE
    cQ
    cR
    cP
    cT
    cU
    cS
    cH
    cI
    cG
    c.or
    cK
    c.le
    c.an
    cO
    @4
    @8
    vc
    vd
    @10
    biid
    dalem.l
    dalem.j
    dalem.a
    @14
    biid
    dalem58.m
    dalem58.o
    @4
    eqid
    @8
    eqid
    dalem58.e
    dalem58.h
    dalem58.i
    dalem58.g
    @5
    eqid
    dalem57
    syl3anc
    @1
    @5
    cG
    cH
    c.or
    co
    cI
    c.or
    co
    #
    cY
    c.an
    co
    cB
    @1
    @2
    @15
    @4
    cY
    c.an
    @1
    @6
    cH
    cA
    wcel
    cI
    cA
    wcel
    cG
    cA
    wcel
    @2
    @15
    wceq
    wph
    @0
    @6
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
    3ad2ant1
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
    cH
    c.or
    cK
    c.le
    c.an
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
    dalem58.m
    dalem58.o
    dalem58.y
    dalem58.z
    dalem58.h
    dalem29
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
    cI
    c.or
    cK
    c.le
    c.an
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
    dalem58.m
    dalem58.o
    dalem58.y
    dalem58.z
    dalem58.i
    dalem34
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
    cG
    c.or
    cK
    c.le
    c.an
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
    dalem58.m
    dalem58.o
    dalem58.y
    dalem58.z
    dalem58.g
    dalem23
    cA
    cH
    cI
    cG
    c.or
    cK
    dalem.j
    dalem.a
    hlatjrot
    syl13anc
    wph
    @0
    @4
    cY
    wceq
    wps
    wph
    @4
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
    dalem.ph
    dalem.j
    dalem.a
    dalemqrprot
    dalem58.y
    syl6eqr
    3ad2ant1
    oveq12d
    dalem58.b1
    syl6eqr
    breqtrd
end
