include "wceq.mm"
include "w3a.mm"
include "co.mm"
include "wbr.mm"
include "dalem57.mm"
include "dalem58.mm"
include "clat.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "wa.mm"
include "wb.mm"
include "dalemkelat.mm"
include "3ad2ant1.mm"
include "dalemdea.mm"
include "eqid.mm"
include "atbase.mm"
include "syl.mm"
include "dalemeea.mm"
include "clln.mm"
include "dalem53.mm"
include "llnbase.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "chlt.mm"
include "dalemkehl.mm"
include "wne.mm"
include "dalemdnee.mm"
include "llni2.mm"
include "syl31anc.mm"
include "llncmp.mm"
include "syl3anc.mm"
include "mpbid.mm"

theorem dalem60
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
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
  assume dalem60.m: |- ./\ = ( meet ` K )
  assume dalem60.o: |- O = ( LPlanes ` K )
  assume dalem60.y: |- Y = ( ( P .\/ Q ) .\/ R )
  assume dalem60.z: |- Z = ( ( S .\/ T ) .\/ U )
  assume dalem60.d: |- D = ( ( P .\/ Q ) ./\ ( S .\/ T ) )
  assume dalem60.e: |- E = ( ( Q .\/ R ) ./\ ( T .\/ U ) )
  assume dalem60.g: |- G = ( ( c .\/ P ) ./\ ( d .\/ S ) )
  assume dalem60.h: |- H = ( ( c .\/ Q ) ./\ ( d .\/ T ) )
  assume dalem60.i: |- I = ( ( c .\/ R ) ./\ ( d .\/ U ) )
  assume dalem60.b1: |- B = ( ( ( G .\/ H ) .\/ I ) ./\ Y )


  assert |- ( ( ph /\ Y = Z /\ ps ) -> ( D .\/ E ) = B )

  proof
    wph
    cY
    cZ
    wceq
    #
    wps
    w3a
    #
    cD
    cE
    c.or
    co
    #
    cB
    c.le
    wbr
    #
    @2
    cB
    wceq
    #
    @1
    cD
    cB
    c.le
    wbr
    #
    cE
    cB
    c.le
    wbr
    #
    @3
    wph
    wps
    cA
    cB
    cC
    cD
    cP
    cQ
    cR
    cS
    cT
    cU
    cG
    cH
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
    dalem60.m
    dalem60.o
    dalem60.y
    dalem60.z
    dalem60.d
    dalem60.g
    dalem60.h
    dalem60.i
    dalem60.b1
    dalem57
    wph
    wps
    cA
    cB
    cC
    cP
    cQ
    cR
    cS
    cT
    cU
    cE
    cG
    cH
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
    dalem60.m
    dalem60.o
    dalem60.y
    dalem60.z
    dalem60.e
    dalem60.g
    dalem60.h
    dalem60.i
    dalem60.b1
    dalem58
    @1
    cK
    clat
    wcel
    #
    cD
    cK
    cbs
    cfv
    #
    wcel
    #
    cE
    @8
    wcel
    #
    cB
    @8
    wcel
    #
    @5
    @6
    wa
    @3
    wb
    wph
    @0
    @7
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
    dalemkelat
    3ad2ant1
    wph
    @0
    @9
    wps
    wph
    cD
    cA
    wcel
    #
    @9
    wph
    cA
    cC
    cD
    cP
    cQ
    cR
    cS
    cT
    cU
    c.or
    cK
    c.le
    c.an
    cO
    cY
    cZ
    dalem.ph
    dalem.l
    dalem.j
    dalem.a
    dalem60.m
    dalem60.o
    dalem60.y
    dalem60.z
    dalem60.d
    dalemdea
    #
    cA
    @8
    cD
    cK
    @8
    eqid
    #
    dalem.a
    atbase
    syl
    3ad2ant1
    wph
    @0
    @10
    wps
    wph
    cE
    cA
    wcel
    #
    @10
    wph
    cA
    cC
    cP
    cQ
    cR
    cS
    cT
    cU
    cE
    c.or
    cK
    c.le
    c.an
    cO
    cY
    cZ
    dalem.ph
    dalem.l
    dalem.j
    dalem.a
    dalem60.m
    dalem60.o
    dalem60.y
    dalem60.z
    dalem60.e
    dalemeea
    #
    cA
    @8
    cE
    cK
    @14
    dalem.a
    atbase
    syl
    3ad2ant1
    @1
    cB
    cK
    clln
    cfv
    #
    wcel
    #
    @11
    wph
    wps
    cA
    cB
    cC
    cP
    cQ
    cR
    cS
    cT
    cU
    cG
    cH
    cI
    c.or
    cK
    c.le
    c.an
    @17
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
    dalem60.m
    @17
    eqid
    #
    dalem60.o
    dalem60.y
    dalem60.z
    dalem60.g
    dalem60.h
    dalem60.i
    dalem60.b1
    dalem53
    #
    @8
    cK
    @17
    cB
    @14
    @19
    llnbase
    syl
    @8
    c.or
    cK
    c.le
    cD
    cE
    cB
    @14
    dalem.l
    dalem.j
    latjle12
    syl13anc
    mpbi2and
    @1
    cK
    chlt
    wcel
    #
    @2
    @17
    wcel
    #
    @18
    @3
    @4
    wb
    wph
    @0
    @21
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
    #
    3ad2ant1
    wph
    @0
    @22
    wps
    wph
    @21
    @12
    @15
    cD
    cE
    wne
    @22
    @23
    @13
    @16
    wph
    cA
    cC
    cD
    cP
    cQ
    cR
    cS
    cT
    cU
    cE
    c.or
    cK
    c.le
    c.an
    cO
    cY
    cZ
    dalem.ph
    dalem.l
    dalem.j
    dalem.a
    dalem60.m
    dalem60.o
    dalem60.y
    dalem60.z
    dalem60.d
    dalem60.e
    dalemdnee
    cA
    cD
    cE
    c.or
    cK
    @17
    dalem.j
    dalem.a
    @19
    llni2
    syl31anc
    3ad2ant1
    @20
    cK
    c.le
    @17
    @2
    cB
    dalem.l
    @19
    llncmp
    syl3anc
    mpbid
end
