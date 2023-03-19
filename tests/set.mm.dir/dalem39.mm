include "wceq.mm"
include "w3a.mm"
include "co.mm"
include "wbr.mm"
include "cv.mm"
include "chlt.mm"
include "wcel.mm"
include "clvol.mm"
include "cfv.mm"
include "wn.mm"
include "dalemkehl.mm"
include "3ad2ant1.mm"
include "dalemyeo.mm"
include "dalemccea.mm"
include "3ad2ant3.mm"
include "dalem-ccly.mm"
include "eqid.mm"
include "lvoli3.mm"
include "syl31anc.mm"
include "dalem34.mm"
include "dalem23.mm"
include "lvolnle3at.mm"
include "syl23anc.mm"
include "wa.mm"
include "dalem38.mm"
include "clat.mm"
include "cbs.mm"
include "dalemkelat.mm"
include "dalem29.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "atbase.mm"
include "syl.mm"
include "latjcl.mm"
include "dalemcceb.mm"
include "latlej2.mm"
include "wb.mm"
include "dalemyeb.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "hlatjrot.mm"
include "oveq1d.mm"
include "breqtrd.mm"
include "adantr.mm"
include "latleeqj2.mm"
include "biimpa.mm"
include "mtand.mm"

theorem dalem39
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
  assume dalem38.m: |- ./\ = ( meet ` K )
  assume dalem38.o: |- O = ( LPlanes ` K )
  assume dalem38.y: |- Y = ( ( P .\/ Q ) .\/ R )
  assume dalem38.z: |- Z = ( ( S .\/ T ) .\/ U )
  assume dalem38.g: |- G = ( ( c .\/ P ) ./\ ( d .\/ S ) )
  assume dalem38.h: |- H = ( ( c .\/ Q ) ./\ ( d .\/ T ) )
  assume dalem38.i: |- I = ( ( c .\/ R ) ./\ ( d .\/ U ) )


  assert |- ( ( ph /\ Y = Z /\ ps ) -> -. H .<_ ( I .\/ G ) )

  proof
    wph
    cY
    cZ
    wceq
    #
    wps
    w3a
    #
    cH
    cI
    cG
    c.or
    co
    #
    c.le
    wbr
    #
    cY
    vc
    cv
    #
    c.or
    co
    #
    @2
    @4
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
    #
    @5
    cK
    clvol
    cfv
    #
    wcel
    #
    cI
    cA
    wcel
    #
    cG
    cA
    wcel
    #
    @4
    cA
    wcel
    #
    @7
    wn
    wph
    @0
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
    3ad2ant1
    #
    @1
    @8
    cY
    cO
    wcel
    #
    @13
    @4
    cY
    c.le
    wbr
    wn
    #
    @10
    @14
    wph
    @0
    @15
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
    dalemyeo
    3ad2ant1
    wps
    wph
    @13
    @0
    wps
    cA
    cC
    c.or
    c.le
    cY
    vc
    vd
    dalem.ps
    dalemccea
    3ad2ant3
    #
    wps
    wph
    @16
    @0
    wps
    cA
    cC
    c.or
    c.le
    cY
    vc
    vd
    dalem.ps
    dalem-ccly
    3ad2ant3
    cA
    cO
    @4
    c.or
    cK
    c.le
    @9
    cY
    dalem.l
    dalem.j
    dalem.a
    dalem38.o
    @9
    eqid
    #
    lvoli3
    syl31anc
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
    dalem38.m
    dalem38.o
    dalem38.y
    dalem38.z
    dalem38.i
    dalem34
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
    dalem38.m
    dalem38.o
    dalem38.y
    dalem38.z
    dalem38.g
    dalem23
    #
    @17
    cA
    cI
    cG
    @4
    c.or
    cK
    c.le
    @9
    @5
    dalem.l
    dalem.j
    dalem.a
    @18
    lvolnle3at
    syl23anc
    @1
    @3
    wa
    #
    @5
    @2
    cH
    c.or
    co
    #
    @4
    c.or
    co
    #
    @6
    c.le
    @1
    @5
    @23
    c.le
    wbr
    @3
    @1
    @5
    cG
    cH
    c.or
    co
    #
    cI
    c.or
    co
    #
    @4
    c.or
    co
    #
    @23
    c.le
    @1
    cY
    @26
    c.le
    wbr
    #
    @4
    @26
    c.le
    wbr
    #
    @5
    @26
    c.le
    wbr
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
    dalem38.m
    dalem38.o
    dalem38.y
    dalem38.z
    dalem38.g
    dalem38.h
    dalem38.i
    dalem38
    @1
    cK
    clat
    wcel
    #
    @25
    cK
    cbs
    cfv
    #
    wcel
    #
    @4
    @31
    wcel
    #
    @28
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
    dalemkelat
    3ad2ant1
    #
    @1
    @30
    @24
    @31
    wcel
    #
    cI
    @31
    wcel
    #
    @32
    @34
    @1
    @8
    @12
    cH
    cA
    wcel
    #
    @35
    @14
    @20
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
    dalem38.m
    dalem38.o
    dalem38.y
    dalem38.z
    dalem38.h
    dalem29
    #
    cA
    @31
    c.or
    cK
    cG
    cH
    @31
    eqid
    #
    dalem.j
    dalem.a
    hlatjcl
    syl3anc
    @1
    @11
    @36
    @19
    cA
    @31
    cI
    cK
    @39
    dalem.a
    atbase
    syl
    @31
    c.or
    cK
    @24
    cI
    @39
    dalem.j
    latjcl
    syl3anc
    #
    wps
    wph
    @33
    @0
    wps
    cA
    cC
    c.or
    cK
    c.le
    cY
    vc
    vd
    dalem.ps
    dalem.a
    dalemcceb
    3ad2ant3
    #
    @31
    c.or
    cK
    c.le
    @25
    @4
    @39
    dalem.l
    dalem.j
    latlej2
    syl3anc
    @1
    @30
    cY
    @31
    wcel
    #
    @33
    @26
    @31
    wcel
    #
    @27
    @28
    wa
    @29
    wb
    @34
    wph
    @0
    @42
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
    dalem38.o
    dalemyeb
    3ad2ant1
    @41
    @1
    @30
    @32
    @33
    @43
    @34
    @40
    @41
    @31
    c.or
    cK
    @25
    @4
    @39
    dalem.j
    latjcl
    syl3anc
    @31
    c.or
    cK
    c.le
    cY
    @4
    @26
    @39
    dalem.l
    dalem.j
    latjle12
    syl13anc
    mpbi2and
    @1
    @25
    @22
    @4
    c.or
    @1
    @8
    @12
    @37
    @11
    @25
    @22
    wceq
    @14
    @20
    @38
    @19
    cA
    cG
    cH
    cI
    c.or
    cK
    dalem.j
    dalem.a
    hlatjrot
    syl13anc
    oveq1d
    breqtrd
    adantr
    @21
    @22
    @2
    @4
    c.or
    @1
    @3
    @22
    @2
    wceq
    #
    @1
    @30
    cH
    @31
    wcel
    #
    @2
    @31
    wcel
    #
    @3
    @44
    wb
    @34
    @1
    @37
    @45
    @38
    cA
    @31
    cH
    cK
    @39
    dalem.a
    atbase
    syl
    @1
    @8
    @11
    @12
    @46
    @14
    @19
    @20
    cA
    @31
    c.or
    cK
    cI
    cG
    @39
    dalem.j
    dalem.a
    hlatjcl
    syl3anc
    @31
    c.or
    cK
    c.le
    cH
    @2
    @39
    dalem.l
    dalem.j
    latleeqj2
    syl3anc
    biimpa
    oveq1d
    breqtrd
    mtand
end
