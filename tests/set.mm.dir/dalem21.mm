include "wceq.mm"
include "w3a.mm"
include "chlt.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "clln.mm"
include "cfv.mm"
include "wne.mm"
include "cp0.mm"
include "dalemkehl.mm"
include "3ad2ant1.mm"
include "dalemcjden.mm"
include "3adant2.mm"
include "dalempjsen.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "dalemply.mm"
include "adantr.mm"
include "dalemsly.mm"
include "wb.mm"
include "clat.mm"
include "cbs.mm"
include "dalemkelat.mm"
include "dalempeb.mm"
include "dalemseb.mm"
include "dalemyeb.mm"
include "eqid.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "3adant3.mm"
include "dalem-ccly.mm"
include "adantl.mm"
include "dalemcceb.mm"
include "dalemddea.mm"
include "atbase.mm"
include "syl.mm"
include "latlej1.mm"
include "syl3anc.mm"
include "wi.mm"
include "llnbase.mm"
include "lattr.mm"
include "mpand.mm"
include "mtod.mm"
include "nbrne2.mm"
include "syl2anc.mm"
include "necomd.mm"
include "cal.mm"
include "hlatl.mm"
include "dalempea.mm"
include "dalemsea.mm"
include "hlatjcl.mm"
include "latmcl.mm"
include "dalemcea.mm"
include "dalemclccjdd.mm"
include "dalemclpjs.mm"
include "dalemceb.mm"
include "latlem12.mm"
include "atlen0.mm"
include "syl31anc.mm"
include "2llnmat.mm"
include "syl32anc.mm"

theorem dalem21
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
  assume dalem21.m: |- ./\ = ( meet ` K )
  assume dalem21.o: |- O = ( LPlanes ` K )
  assume dalem21.y: |- Y = ( ( P .\/ Q ) .\/ R )
  assume dalem21.z: |- Z = ( ( S .\/ T ) .\/ U )


  assert |- ( ( ph /\ Y = Z /\ ps ) -> ( ( c .\/ d ) ./\ ( P .\/ S ) ) e. A )

  proof
    wph
    cY
    cZ
    wceq
    #
    wps
    w3a
    #
    cK
    chlt
    wcel
    #
    vc
    cv
    #
    vd
    cv
    #
    c.or
    co
    #
    cK
    clln
    cfv
    #
    wcel
    #
    cP
    cS
    c.or
    co
    #
    @6
    wcel
    #
    @5
    @8
    wne
    @5
    @8
    c.an
    co
    #
    cK
    cp0
    cfv
    #
    wne
    #
    @10
    cA
    wcel
    wph
    @0
    @2
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
    wps
    @7
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
    dalemcjden
    #
    3adant2
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
    dalem21.o
    dalem21.y
    dalempjsen
    3ad2ant1
    @1
    @8
    @5
    @1
    @8
    cY
    c.le
    wbr
    #
    @5
    cY
    c.le
    wbr
    #
    wn
    #
    @8
    @5
    wne
    wph
    @0
    @15
    wps
    wph
    @0
    wa
    cP
    cY
    c.le
    wbr
    #
    cS
    cY
    c.le
    wbr
    #
    @15
    wph
    @18
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
    dalem.ph
    dalem.l
    dalem.j
    dalem.a
    dalem21.o
    dalem21.y
    dalemply
    adantr
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
    dalem21.z
    dalemsly
    wph
    @18
    @19
    wa
    @15
    wb
    #
    @0
    wph
    cK
    clat
    wcel
    #
    cP
    cK
    cbs
    cfv
    #
    wcel
    cS
    @22
    wcel
    cY
    @22
    wcel
    #
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
    dalem.ph
    dalem.a
    dalempeb
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
    dalem.ph
    dalem21.o
    dalemyeb
    #
    @22
    c.or
    cK
    c.le
    cP
    cS
    cY
    @22
    eqid
    #
    dalem.l
    dalem.j
    latjle12
    syl13anc
    adantr
    mpbi2and
    3adant3
    wph
    wps
    @17
    @0
    wph
    wps
    wa
    #
    @16
    @3
    cY
    c.le
    wbr
    #
    wps
    @28
    wn
    wph
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
    adantl
    @27
    @3
    @5
    c.le
    wbr
    #
    @16
    @28
    @27
    @21
    @3
    @22
    wcel
    #
    @4
    @22
    wcel
    #
    @29
    wph
    @21
    wps
    @24
    adantr
    #
    wps
    @30
    wph
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
    adantl
    #
    wps
    @31
    wph
    wps
    @4
    cA
    wcel
    @31
    wps
    cA
    cC
    c.or
    c.le
    cY
    vc
    vd
    dalem.ps
    dalemddea
    cA
    @22
    @4
    cK
    @26
    dalem.a
    atbase
    syl
    adantl
    @22
    c.or
    cK
    c.le
    @3
    @4
    @26
    dalem.l
    dalem.j
    latlej1
    syl3anc
    @27
    @21
    @30
    @5
    @22
    wcel
    #
    @23
    @29
    @16
    wa
    @28
    wi
    @32
    @33
    @27
    @7
    @34
    @14
    @22
    cK
    @6
    @5
    @26
    @6
    eqid
    #
    llnbase
    syl
    #
    wph
    @23
    wps
    @25
    adantr
    @22
    cK
    c.le
    @3
    @5
    cY
    @26
    dalem.l
    lattr
    syl13anc
    mpand
    mtod
    3adant2
    @8
    @5
    cY
    c.le
    nbrne2
    syl2anc
    necomd
    wph
    wps
    @12
    @0
    @27
    cK
    cal
    wcel
    #
    @10
    @22
    wcel
    #
    cC
    cA
    wcel
    #
    cC
    @10
    c.le
    wbr
    #
    @12
    wph
    @37
    wps
    wph
    @2
    @37
    @13
    cK
    hlatl
    syl
    adantr
    @27
    @21
    @34
    @8
    @22
    wcel
    #
    @38
    @32
    @36
    wph
    @41
    wps
    wph
    @2
    cP
    cA
    wcel
    cS
    cA
    wcel
    @41
    @13
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
    dalem.ph
    dalemsea
    cA
    @22
    c.or
    cK
    cP
    cS
    @26
    dalem.j
    dalem.a
    hlatjcl
    syl3anc
    adantr
    #
    @22
    cK
    c.an
    @5
    @8
    @26
    dalem21.m
    latmcl
    syl3anc
    wph
    @39
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
    dalem21.o
    dalem21.y
    dalemcea
    adantr
    @27
    cC
    @5
    c.le
    wbr
    #
    cC
    @8
    c.le
    wbr
    #
    @40
    wps
    @43
    wph
    wps
    cA
    cC
    c.or
    c.le
    cY
    vc
    vd
    dalem.ps
    dalemclccjdd
    adantl
    wph
    @44
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
    dalemclpjs
    adantr
    @27
    @21
    cC
    @22
    wcel
    #
    @34
    @41
    @43
    @44
    wa
    @40
    wb
    @32
    wph
    @45
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
    dalem.a
    dalemceb
    adantr
    @36
    @42
    @22
    cK
    c.le
    c.an
    cC
    @5
    @8
    @26
    dalem.l
    dalem21.m
    latlem12
    syl13anc
    mpbi2and
    cA
    @22
    cC
    cK
    c.le
    @10
    @11
    @26
    dalem.l
    @11
    eqid
    #
    dalem.a
    atlen0
    syl31anc
    3adant2
    cA
    cK
    c.an
    @6
    @5
    @8
    @11
    dalem21.m
    @46
    dalem.a
    @35
    2llnmat
    syl32anc
end
