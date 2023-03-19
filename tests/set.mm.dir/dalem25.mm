include "wceq.mm"
include "w3a.mm"
include "wne.mm"
include "cv.mm"
include "dalemcnes.mm"
include "3ad2ant1.mm"
include "wa.mm"
include "wbr.mm"
include "co.mm"
include "dalemclccjdd.mm"
include "3ad2ant3.mm"
include "adantr.mm"
include "simpr.mm"
include "clat.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "dalemkelat.mm"
include "chlt.mm"
include "dalemkehl.mm"
include "dalemccea.mm"
include "dalempea.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "dalemddea.mm"
include "dalemsea.mm"
include "latmle2.mm"
include "syl5eqbr.mm"
include "hlatjcom.mm"
include "breqtrd.mm"
include "eqbrtrd.mm"
include "hlatlej2.mm"
include "wb.mm"
include "dalemcceb.mm"
include "atbase.mm"
include "syl.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "wi.mm"
include "dalemceb.mm"
include "lattr.mm"
include "mp2and.mm"
include "dalemyeb.mm"
include "latmlem1.mm"
include "mpd.mm"
include "dalem17.mm"
include "3adant3.mm"
include "latleeqm1.mm"
include "mpbid.mm"
include "wn.mm"
include "dalemsly.mm"
include "dalem-ddly.mm"
include "2atjm.mm"
include "syl132anc.mm"
include "3brtr3d.mm"
include "cal.mm"
include "hlatl.mm"
include "dalemcea.mm"
include "atcmp.mm"
include "ex.mm"
include "necon3d.mm"

theorem dalem25
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
  assume dalem23.m: |- ./\ = ( meet ` K )
  assume dalem23.o: |- O = ( LPlanes ` K )
  assume dalem23.y: |- Y = ( ( P .\/ Q ) .\/ R )
  assume dalem23.z: |- Z = ( ( S .\/ T ) .\/ U )
  assume dalem23.g: |- G = ( ( c .\/ P ) ./\ ( d .\/ S ) )


  assert |- ( ( ph /\ Y = Z /\ ps ) -> c =/= G )

  proof
    wph
    cY
    cZ
    wceq
    #
    wps
    w3a
    #
    cC
    cS
    wne
    #
    vc
    cv
    #
    cG
    wne
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
    dalem.l
    dalem.j
    dalem.a
    dalemcnes
    3ad2ant1
    @1
    @3
    cG
    cC
    cS
    @1
    @3
    cG
    wceq
    #
    cC
    cS
    wceq
    #
    @1
    @4
    wa
    #
    cC
    cS
    c.le
    wbr
    #
    @5
    @6
    cC
    cY
    c.an
    co
    #
    cS
    vd
    cv
    #
    c.or
    co
    #
    cY
    c.an
    co
    #
    cC
    cS
    c.le
    @6
    cC
    @10
    c.le
    wbr
    #
    @8
    @11
    c.le
    wbr
    #
    @6
    cC
    @3
    @9
    c.or
    co
    #
    c.le
    wbr
    #
    @14
    @10
    c.le
    wbr
    #
    @12
    @1
    @15
    @4
    wps
    wph
    @15
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
    dalemclccjdd
    3ad2ant3
    adantr
    @6
    @3
    @10
    c.le
    wbr
    #
    @9
    @10
    c.le
    wbr
    #
    @16
    @6
    @3
    cG
    @10
    c.le
    @1
    @4
    simpr
    @1
    cG
    @10
    c.le
    wbr
    @4
    @1
    cG
    @9
    cS
    c.or
    co
    #
    @10
    c.le
    @1
    cG
    @3
    cP
    c.or
    co
    #
    @19
    c.an
    co
    #
    @19
    c.le
    dalem23.g
    @1
    cK
    clat
    wcel
    #
    @20
    cK
    cbs
    cfv
    #
    wcel
    #
    @19
    @23
    wcel
    #
    @21
    @19
    c.le
    wbr
    wph
    @0
    @22
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
    @3
    cA
    wcel
    #
    cP
    cA
    wcel
    #
    @24
    wph
    @0
    @27
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
    #
    wps
    wph
    @28
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
    wph
    @0
    @29
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
    dalempea
    3ad2ant1
    cA
    @23
    c.or
    cK
    @3
    cP
    @23
    eqid
    #
    dalem.j
    dalem.a
    hlatjcl
    syl3anc
    @1
    @27
    @9
    cA
    wcel
    #
    cS
    cA
    wcel
    #
    @25
    @31
    wps
    wph
    @34
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
    dalemddea
    #
    3ad2ant3
    #
    wph
    @0
    @35
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
    dalemsea
    #
    3ad2ant1
    #
    cA
    @23
    c.or
    cK
    @9
    cS
    @33
    dalem.j
    dalem.a
    hlatjcl
    syl3anc
    @23
    cK
    c.le
    c.an
    @20
    @19
    @33
    dalem.l
    dalem23.m
    latmle2
    syl3anc
    syl5eqbr
    @1
    @27
    @34
    @35
    @19
    @10
    wceq
    @31
    @37
    @39
    cA
    c.or
    cK
    @9
    cS
    dalem.j
    dalem.a
    hlatjcom
    syl3anc
    breqtrd
    adantr
    eqbrtrd
    @1
    @18
    @4
    @1
    @27
    @35
    @34
    @18
    @31
    @39
    @37
    cA
    cS
    @9
    c.or
    cK
    c.le
    dalem.l
    dalem.j
    dalem.a
    hlatlej2
    syl3anc
    adantr
    @1
    @17
    @18
    wa
    @16
    wb
    #
    @4
    @1
    @22
    @3
    @23
    wcel
    #
    @9
    @23
    wcel
    #
    @10
    @23
    wcel
    #
    @40
    @26
    wps
    wph
    @41
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
    wps
    wph
    @42
    @0
    wps
    @34
    @42
    @36
    cA
    @23
    @9
    cK
    @33
    dalem.a
    atbase
    syl
    3ad2ant3
    @1
    @27
    @35
    @34
    @43
    @31
    @39
    @37
    cA
    @23
    c.or
    cK
    cS
    @9
    @33
    dalem.j
    dalem.a
    hlatjcl
    syl3anc
    #
    @23
    c.or
    cK
    c.le
    @3
    @9
    @10
    @33
    dalem.l
    dalem.j
    latjle12
    syl13anc
    adantr
    mpbi2and
    @1
    @15
    @16
    wa
    @12
    wi
    #
    @4
    @1
    @22
    cC
    @23
    wcel
    #
    @14
    @23
    wcel
    #
    @43
    @45
    @26
    wph
    @0
    @46
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
    3ad2ant1
    #
    @1
    @27
    @28
    @34
    @47
    @31
    @32
    @37
    cA
    @23
    c.or
    cK
    @3
    @9
    @33
    dalem.j
    dalem.a
    hlatjcl
    syl3anc
    @44
    @23
    cK
    c.le
    cC
    @14
    @10
    @33
    dalem.l
    lattr
    syl13anc
    adantr
    mp2and
    @1
    @12
    @13
    wi
    #
    @4
    @1
    @22
    @46
    @43
    cY
    @23
    wcel
    #
    @49
    @26
    @48
    @44
    wph
    @0
    @50
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
    dalem23.o
    dalemyeb
    3ad2ant1
    #
    @23
    cK
    c.le
    c.an
    cC
    @10
    cY
    @33
    dalem.l
    dalem23.m
    latmlem1
    syl13anc
    adantr
    mpd
    @1
    @8
    cC
    wceq
    #
    @4
    @1
    cC
    cY
    c.le
    wbr
    #
    @52
    wph
    @0
    @53
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
    dalem23.o
    dalem23.y
    dalem23.z
    dalem17
    3adant3
    @1
    @22
    @46
    @50
    @53
    @52
    wb
    @26
    @48
    @51
    @23
    cK
    c.le
    c.an
    cC
    cY
    @33
    dalem.l
    dalem23.m
    latleeqm1
    syl3anc
    mpbid
    adantr
    @1
    @11
    cS
    wceq
    #
    @4
    @1
    @27
    @35
    @34
    @50
    cS
    cY
    c.le
    wbr
    #
    @9
    cY
    c.le
    wbr
    wn
    #
    @54
    @31
    @39
    @37
    @51
    wph
    @0
    @55
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
    dalem23.z
    dalemsly
    3adant3
    wps
    wph
    @56
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
    dalem-ddly
    3ad2ant3
    cA
    @23
    cS
    @9
    c.or
    cK
    c.le
    c.an
    cY
    @33
    dalem.l
    dalem.j
    dalem23.m
    dalem.a
    2atjm
    syl132anc
    adantr
    3brtr3d
    @1
    @7
    @5
    wb
    #
    @4
    wph
    @0
    @57
    wps
    wph
    cK
    cal
    wcel
    #
    cC
    cA
    wcel
    @35
    @57
    wph
    @27
    @58
    @30
    cK
    hlatl
    syl
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
    dalem23.o
    dalem23.y
    dalemcea
    @38
    cA
    cC
    cS
    cK
    c.le
    dalem.l
    dalem.a
    atcmp
    syl3anc
    3ad2ant1
    adantr
    mpbid
    ex
    necon3d
    mpd
end
