include "wceq.mm"
include "w3a.mm"
include "co.mm"
include "wbr.mm"
include "clat.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "dalemkelat.mm"
include "3ad2ant1.mm"
include "chlt.mm"
include "dalemkehl.mm"
include "dalem23.mm"
include "dalem29.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "dalempjqeb.mm"
include "latmle1.mm"
include "dalem34.mm"
include "atbase.mm"
include "syl.mm"
include "latlej1.mm"
include "dalemreb.mm"
include "syl6breqr.mm"
include "wa.mm"
include "wi.mm"
include "dalem42.mm"
include "lplnbase.mm"
include "dalemyeb.mm"
include "latmlem12.mm"
include "syl122anc.mm"
include "mp2and.mm"
include "wb.mm"
include "latmcl.mm"
include "clln.mm"
include "dalem53.mm"
include "llnbase.mm"
include "latlem12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "cal.mm"
include "hlatl.mm"
include "dalem52.mm"
include "dalem54.mm"
include "atcmp.mm"
include "mpbid.mm"

theorem dalem55
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
  assume dalem54.m: |- ./\ = ( meet ` K )
  assume dalem54.o: |- O = ( LPlanes ` K )
  assume dalem54.y: |- Y = ( ( P .\/ Q ) .\/ R )
  assume dalem54.z: |- Z = ( ( S .\/ T ) .\/ U )
  assume dalem54.g: |- G = ( ( c .\/ P ) ./\ ( d .\/ S ) )
  assume dalem54.h: |- H = ( ( c .\/ Q ) ./\ ( d .\/ T ) )
  assume dalem54.i: |- I = ( ( c .\/ R ) ./\ ( d .\/ U ) )
  assume dalem54.b1: |- B = ( ( ( G .\/ H ) .\/ I ) ./\ Y )


  assert |- ( ( ph /\ Y = Z /\ ps ) -> ( ( G .\/ H ) ./\ ( P .\/ Q ) ) = ( ( G .\/ H ) ./\ B ) )

  proof
    wph
    cY
    cZ
    wceq
    #
    wps
    w3a
    #
    cG
    cH
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
    @2
    cB
    c.an
    co
    #
    c.le
    wbr
    #
    @4
    @5
    wceq
    #
    @1
    @4
    @2
    c.le
    wbr
    #
    @4
    cB
    c.le
    wbr
    #
    @6
    @1
    cK
    clat
    wcel
    #
    @2
    cK
    cbs
    cfv
    #
    wcel
    #
    @3
    @11
    wcel
    #
    @8
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
    dalemkelat
    #
    3ad2ant1
    #
    @1
    cK
    chlt
    wcel
    #
    cG
    cA
    wcel
    cH
    cA
    wcel
    @12
    wph
    @0
    @16
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
    dalem54.m
    dalem54.o
    dalem54.y
    dalem54.z
    dalem54.g
    dalem23
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
    dalem54.m
    dalem54.o
    dalem54.y
    dalem54.z
    dalem54.h
    dalem29
    cA
    @11
    c.or
    cK
    cG
    cH
    @11
    eqid
    #
    dalem.j
    dalem.a
    hlatjcl
    syl3anc
    #
    wph
    @0
    @13
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
    dalem.j
    dalem.a
    dalempjqeb
    #
    3ad2ant1
    #
    @11
    cK
    c.le
    c.an
    @2
    @3
    @18
    dalem.l
    dalem54.m
    latmle1
    syl3anc
    @1
    @4
    @2
    cI
    c.or
    co
    #
    cY
    c.an
    co
    #
    cB
    c.le
    @1
    @2
    @22
    c.le
    wbr
    #
    @3
    cY
    c.le
    wbr
    #
    @4
    @23
    c.le
    wbr
    #
    @1
    @10
    @12
    cI
    @11
    wcel
    #
    @24
    @15
    @19
    @1
    cI
    cA
    wcel
    @27
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
    dalem54.m
    dalem54.o
    dalem54.y
    dalem54.z
    dalem54.i
    dalem34
    cA
    @11
    cI
    cK
    @18
    dalem.a
    atbase
    syl
    @11
    c.or
    cK
    c.le
    @2
    cI
    @18
    dalem.l
    dalem.j
    latlej1
    syl3anc
    wph
    @0
    @25
    wps
    wph
    @3
    @3
    cR
    c.or
    co
    #
    cY
    c.le
    wph
    @10
    @13
    cR
    @11
    wcel
    @3
    @28
    c.le
    wbr
    @14
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
    dalem.ph
    dalem.a
    dalemreb
    @11
    c.or
    cK
    c.le
    @3
    cR
    @18
    dalem.l
    dalem.j
    latlej1
    syl3anc
    dalem54.y
    syl6breqr
    3ad2ant1
    @1
    @10
    @12
    @22
    @11
    wcel
    #
    @13
    cY
    @11
    wcel
    #
    @24
    @25
    wa
    @26
    wi
    @15
    @19
    @1
    @22
    cO
    wcel
    @29
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
    dalem54.m
    dalem54.o
    dalem54.y
    dalem54.z
    dalem54.g
    dalem54.h
    dalem54.i
    dalem42
    @11
    cO
    cK
    @22
    @18
    dalem54.o
    lplnbase
    syl
    @21
    wph
    @0
    @30
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
    dalem54.o
    dalemyeb
    3ad2ant1
    @11
    cK
    c.le
    c.an
    cY
    @2
    @22
    @3
    @18
    dalem.l
    dalem54.m
    latmlem12
    syl122anc
    mp2and
    dalem54.b1
    syl6breqr
    @1
    @10
    @4
    @11
    wcel
    #
    @12
    cB
    @11
    wcel
    #
    @8
    @9
    wa
    @6
    wb
    @15
    @1
    @10
    @12
    @13
    @31
    @15
    @19
    @21
    @11
    cK
    c.an
    @2
    @3
    @18
    dalem54.m
    latmcl
    syl3anc
    @19
    @1
    cB
    cK
    clln
    cfv
    #
    wcel
    @32
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
    @33
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
    dalem54.m
    @33
    eqid
    #
    dalem54.o
    dalem54.y
    dalem54.z
    dalem54.g
    dalem54.h
    dalem54.i
    dalem54.b1
    dalem53
    @11
    cK
    @33
    cB
    @18
    @34
    llnbase
    syl
    @11
    cK
    c.le
    c.an
    @4
    @2
    cB
    @18
    dalem.l
    dalem54.m
    latlem12
    syl13anc
    mpbi2and
    @1
    cK
    cal
    wcel
    #
    @4
    cA
    wcel
    @5
    cA
    wcel
    @6
    @7
    wb
    @1
    @16
    @35
    @17
    cK
    hlatl
    syl
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
    dalem54.m
    dalem54.o
    dalem54.y
    dalem54.z
    dalem54.g
    dalem54.h
    dalem54.i
    dalem52
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
    dalem54.m
    dalem54.o
    dalem54.y
    dalem54.z
    dalem54.g
    dalem54.h
    dalem54.i
    dalem54.b1
    dalem54
    cA
    @4
    @5
    cK
    c.le
    dalem.l
    dalem.a
    atcmp
    syl3anc
    mpbid
end
