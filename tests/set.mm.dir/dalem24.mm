include "wceq.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "cp0.mm"
include "cfv.mm"
include "cv.mm"
include "oveq1i.mm"
include "col.mm"
include "wcel.mm"
include "cbs.mm"
include "chlt.mm"
include "dalemkehl.mm"
include "hlol.mm"
include "syl.mm"
include "3ad2ant1.mm"
include "dalemccea.mm"
include "3ad2ant3.mm"
include "dalempea.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "dalemddea.mm"
include "dalemsea.mm"
include "dalemyeb.mm"
include "latmmdir.mm"
include "syl13anc.mm"
include "syl5eq.mm"
include "hlatjcom.mm"
include "oveq1d.mm"
include "dalemply.mm"
include "dalem-ccly.mm"
include "2atjm.mm"
include "syl132anc.mm"
include "eqtrd.mm"
include "dalemsly.mm"
include "3adant3.mm"
include "dalem-ddly.mm"
include "oveq12d.mm"
include "wne.mm"
include "dalempnes.mm"
include "cal.mm"
include "wb.mm"
include "hlatl.mm"
include "atnem0.mm"
include "mpbid.mm"
include "3eqtrd.mm"
include "dalem23.mm"
include "atnle.mm"
include "mpbird.mm"

theorem dalem24
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


  assert |- ( ( ph /\ Y = Z /\ ps ) -> -. G .<_ Y )

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
    cY
    c.le
    wbr
    wn
    #
    cG
    cY
    c.an
    co
    #
    cK
    cp0
    cfv
    #
    wceq
    #
    @1
    @3
    vc
    cv
    #
    cP
    c.or
    co
    #
    cY
    c.an
    co
    #
    vd
    cv
    #
    cS
    c.or
    co
    #
    cY
    c.an
    co
    #
    c.an
    co
    #
    cP
    cS
    c.an
    co
    #
    @4
    @1
    @3
    @7
    @10
    c.an
    co
    #
    cY
    c.an
    co
    #
    @12
    cG
    @14
    cY
    c.an
    dalem23.g
    oveq1i
    @1
    cK
    col
    wcel
    #
    @7
    cK
    cbs
    cfv
    #
    wcel
    #
    @10
    @17
    wcel
    #
    cY
    @17
    wcel
    #
    @15
    @12
    wceq
    wph
    @0
    @16
    wps
    wph
    cK
    chlt
    wcel
    #
    @16
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
    cK
    hlol
    syl
    3ad2ant1
    @1
    @21
    @6
    cA
    wcel
    #
    cP
    cA
    wcel
    #
    @18
    wph
    @0
    @21
    wps
    @22
    3ad2ant1
    #
    wps
    wph
    @23
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
    dalempea
    #
    3ad2ant1
    #
    cA
    @17
    c.or
    cK
    @6
    cP
    @17
    eqid
    #
    dalem.j
    dalem.a
    hlatjcl
    syl3anc
    @1
    @21
    @9
    cA
    wcel
    #
    cS
    cA
    wcel
    #
    @19
    @25
    wps
    wph
    @30
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
    3ad2ant3
    #
    wph
    @0
    @31
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
    @17
    c.or
    cK
    @9
    cS
    @29
    dalem.j
    dalem.a
    hlatjcl
    syl3anc
    wph
    @0
    @20
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
    @17
    cK
    c.an
    @7
    @10
    cY
    @29
    dalem23.m
    latmmdir
    syl13anc
    syl5eq
    @1
    @8
    cP
    @11
    cS
    c.an
    @1
    @8
    cP
    @6
    c.or
    co
    #
    cY
    c.an
    co
    #
    cP
    @1
    @7
    @36
    cY
    c.an
    @1
    @21
    @23
    @24
    @7
    @36
    wceq
    @25
    @26
    @28
    cA
    c.or
    cK
    @6
    cP
    dalem.j
    dalem.a
    hlatjcom
    syl3anc
    oveq1d
    @1
    @21
    @24
    @23
    @20
    cP
    cY
    c.le
    wbr
    #
    @6
    cY
    c.le
    wbr
    wn
    #
    @37
    cP
    wceq
    @25
    @28
    @26
    @35
    wph
    @0
    @38
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
    dalemply
    3ad2ant1
    wps
    wph
    @39
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
    @17
    cP
    @6
    c.or
    cK
    c.le
    c.an
    cY
    @29
    dalem.l
    dalem.j
    dalem23.m
    dalem.a
    2atjm
    syl132anc
    eqtrd
    @1
    @11
    cS
    @9
    c.or
    co
    #
    cY
    c.an
    co
    #
    cS
    @1
    @10
    @40
    cY
    c.an
    @1
    @21
    @30
    @31
    @10
    @40
    wceq
    @25
    @32
    @34
    cA
    c.or
    cK
    @9
    cS
    dalem.j
    dalem.a
    hlatjcom
    syl3anc
    oveq1d
    @1
    @21
    @31
    @30
    @20
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
    @41
    cS
    wceq
    @25
    @34
    @32
    @35
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
    dalem.l
    dalem.j
    dalem.a
    dalem23.z
    dalemsly
    3adant3
    wps
    wph
    @43
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
    @17
    cS
    @9
    c.or
    cK
    c.le
    c.an
    cY
    @29
    dalem.l
    dalem.j
    dalem23.m
    dalem.a
    2atjm
    syl132anc
    eqtrd
    oveq12d
    wph
    @0
    @13
    @4
    wceq
    #
    wps
    wph
    cP
    cS
    wne
    #
    @44
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
    dalempnes
    wph
    cK
    cal
    wcel
    #
    @24
    @31
    @45
    @44
    wb
    wph
    @21
    @46
    @22
    cK
    hlatl
    syl
    #
    @27
    @33
    cA
    cP
    cS
    cK
    c.an
    @4
    dalem23.m
    @4
    eqid
    #
    dalem.a
    atnem0
    syl3anc
    mpbid
    3ad2ant1
    3eqtrd
    @1
    @46
    cG
    cA
    wcel
    @20
    @2
    @5
    wb
    wph
    @0
    @46
    wps
    @47
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
    dalem23.m
    dalem23.o
    dalem23.y
    dalem23.z
    dalem23.g
    dalem23
    @35
    cA
    @17
    cG
    cK
    c.le
    c.an
    cY
    @4
    @29
    dalem.l
    dalem23.m
    @48
    dalem.a
    atnle
    syl3anc
    mpbird
end
