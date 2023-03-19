include "wceq.mm"
include "w3a.mm"
include "co.mm"
include "wbr.mm"
include "dalem55.mm"
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
include "latmle2.mm"
include "eqbrtrrd.mm"
include "dalem56.mm"
include "dalemsjteb.mm"
include "wa.mm"
include "wb.mm"
include "dalem54.mm"
include "atbase.mm"
include "syl.mm"
include "latlem12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "syl6breqr.mm"
include "cal.mm"
include "hlatl.mm"
include "dalemdea.mm"
include "atcmp.mm"
include "mpbid.mm"
include "clln.mm"
include "dalem53.mm"
include "llnbase.mm"

theorem dalem57
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
  assume dalem57.m: |- ./\ = ( meet ` K )
  assume dalem57.o: |- O = ( LPlanes ` K )
  assume dalem57.y: |- Y = ( ( P .\/ Q ) .\/ R )
  assume dalem57.z: |- Z = ( ( S .\/ T ) .\/ U )
  assume dalem57.d: |- D = ( ( P .\/ Q ) ./\ ( S .\/ T ) )
  assume dalem57.g: |- G = ( ( c .\/ P ) ./\ ( d .\/ S ) )
  assume dalem57.h: |- H = ( ( c .\/ Q ) ./\ ( d .\/ T ) )
  assume dalem57.i: |- I = ( ( c .\/ R ) ./\ ( d .\/ U ) )
  assume dalem57.b1: |- B = ( ( ( G .\/ H ) .\/ I ) ./\ Y )


  assert |- ( ( ph /\ Y = Z /\ ps ) -> D .<_ B )

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
    cB
    c.an
    co
    #
    cD
    cB
    c.le
    @1
    @3
    cD
    c.le
    wbr
    #
    @3
    cD
    wceq
    #
    @1
    @3
    cP
    cQ
    c.or
    co
    #
    cS
    cT
    c.or
    co
    #
    c.an
    co
    #
    cD
    c.le
    @1
    @3
    @6
    c.le
    wbr
    #
    @3
    @7
    c.le
    wbr
    #
    @3
    @8
    c.le
    wbr
    #
    @1
    @2
    @6
    c.an
    co
    #
    @3
    @6
    c.le
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
    dalem57.m
    dalem57.o
    dalem57.y
    dalem57.z
    dalem57.g
    dalem57.h
    dalem57.i
    dalem57.b1
    dalem55
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
    @6
    @14
    wcel
    #
    @12
    @6
    c.le
    wbr
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
    dalemkelat
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
    @15
    wph
    @0
    @18
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
    dalem57.m
    dalem57.o
    dalem57.y
    dalem57.z
    dalem57.g
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
    dalem57.m
    dalem57.o
    dalem57.y
    dalem57.z
    dalem57.h
    dalem29
    cA
    @14
    c.or
    cK
    cG
    cH
    @14
    eqid
    #
    dalem.j
    dalem.a
    hlatjcl
    syl3anc
    #
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
    dalem.j
    dalem.a
    dalempjqeb
    3ad2ant1
    #
    @14
    cK
    c.le
    c.an
    @2
    @6
    @20
    dalem.l
    dalem57.m
    latmle2
    syl3anc
    eqbrtrrd
    @1
    @2
    @7
    c.an
    co
    #
    @3
    @7
    c.le
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
    dalem57.m
    dalem57.o
    dalem57.y
    dalem57.z
    dalem57.g
    dalem57.h
    dalem57.i
    dalem57.b1
    dalem56
    @1
    @13
    @15
    @7
    @14
    wcel
    #
    @23
    @7
    c.le
    wbr
    @17
    @21
    wph
    @0
    @24
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
    dalemsjteb
    3ad2ant1
    #
    @14
    cK
    c.le
    c.an
    @2
    @7
    @20
    dalem.l
    dalem57.m
    latmle2
    syl3anc
    eqbrtrrd
    @1
    @13
    @3
    @14
    wcel
    #
    @16
    @24
    @9
    @10
    wa
    @11
    wb
    @17
    @1
    @3
    cA
    wcel
    #
    @26
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
    dalem57.m
    dalem57.o
    dalem57.y
    dalem57.z
    dalem57.g
    dalem57.h
    dalem57.i
    dalem57.b1
    dalem54
    #
    cA
    @14
    @3
    cK
    @20
    dalem.a
    atbase
    syl
    @22
    @25
    @14
    cK
    c.le
    c.an
    @3
    @6
    @7
    @20
    dalem.l
    dalem57.m
    latlem12
    syl13anc
    mpbi2and
    dalem57.d
    syl6breqr
    @1
    cK
    cal
    wcel
    #
    @27
    cD
    cA
    wcel
    #
    @4
    @5
    wb
    @1
    @18
    @29
    @19
    cK
    hlatl
    syl
    @28
    wph
    @0
    @30
    wps
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
    dalem57.m
    dalem57.o
    dalem57.y
    dalem57.z
    dalem57.d
    dalemdea
    3ad2ant1
    cA
    @3
    cD
    cK
    c.le
    dalem.l
    dalem.a
    atcmp
    syl3anc
    mpbid
    @1
    @13
    @15
    cB
    @14
    wcel
    #
    @3
    cB
    c.le
    wbr
    @17
    @21
    @1
    cB
    cK
    clln
    cfv
    #
    wcel
    @31
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
    @32
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
    dalem57.m
    @32
    eqid
    #
    dalem57.o
    dalem57.y
    dalem57.z
    dalem57.g
    dalem57.h
    dalem57.i
    dalem57.b1
    dalem53
    @14
    cK
    @32
    cB
    @20
    @33
    llnbase
    syl
    @14
    cK
    c.le
    c.an
    @2
    cB
    @20
    dalem.l
    dalem57.m
    latmle2
    syl3anc
    eqbrtrrd
end
