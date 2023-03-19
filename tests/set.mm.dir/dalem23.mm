include "wceq.mm"
include "w3a.mm"
include "cv.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "chlt.mm"
include "dalemkehl.mm"
include "adantr.mm"
include "dalemccea.mm"
include "adantl.mm"
include "dalempea.mm"
include "dalemddea.mm"
include "dalemsea.mm"
include "hlatj4.mm"
include "syl122anc.mm"
include "3adant2.mm"
include "dalem22.mm"
include "eqeltrd.mm"
include "clln.mm"
include "cfv.mm"
include "wb.mm"
include "3ad2ant1.mm"
include "wne.mm"
include "wbr.mm"
include "wn.mm"
include "dalemply.mm"
include "dalem-ccly.mm"
include "nbrne2.mm"
include "syl2an.mm"
include "necomd.mm"
include "eqid.mm"
include "llni2.mm"
include "syl31anc.mm"
include "3ad2ant3.mm"
include "dalemsly.mm"
include "3adant3.mm"
include "dalem-ddly.mm"
include "syl2anc.mm"
include "2llnmj.mm"
include "syl3anc.mm"
include "mpbird.mm"
include "syl5eqel.mm"

theorem dalem23
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


  assert |- ( ( ph /\ Y = Z /\ ps ) -> G e. A )

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
    vc
    cv
    #
    cP
    c.or
    co
    #
    vd
    cv
    #
    cS
    c.or
    co
    #
    c.an
    co
    #
    cA
    dalem23.g
    @1
    @6
    cA
    wcel
    #
    @3
    @5
    c.or
    co
    #
    cO
    wcel
    #
    @1
    @8
    @2
    @4
    c.or
    co
    cP
    cS
    c.or
    co
    c.or
    co
    #
    cO
    wph
    wps
    @8
    @10
    wceq
    #
    @0
    wph
    wps
    wa
    #
    cK
    chlt
    wcel
    #
    @2
    cA
    wcel
    #
    cP
    cA
    wcel
    #
    @4
    cA
    wcel
    #
    cS
    cA
    wcel
    #
    @11
    wph
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
    dalemkehl
    #
    adantr
    #
    wps
    @14
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
    dalemccea
    adantl
    #
    wph
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
    dalempea
    adantr
    #
    wps
    @16
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
    dalemddea
    #
    adantl
    wph
    @17
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
    adantr
    cA
    @2
    cP
    @4
    cS
    c.or
    cK
    dalem.j
    dalem.a
    hlatj4
    syl122anc
    3adant2
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
    dalem23.o
    dalem23.y
    dalem23.z
    dalem22
    eqeltrd
    @1
    @13
    @3
    cK
    clln
    cfv
    #
    wcel
    #
    @5
    @24
    wcel
    #
    @7
    @9
    wb
    wph
    @0
    @13
    wps
    @18
    3ad2ant1
    #
    wph
    wps
    @25
    @0
    @12
    @13
    @14
    @15
    @2
    cP
    wne
    @25
    @19
    @20
    @21
    @12
    cP
    @2
    wph
    cP
    cY
    c.le
    wbr
    @2
    cY
    c.le
    wbr
    wn
    cP
    @2
    wne
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
    cP
    @2
    cY
    c.le
    nbrne2
    syl2an
    necomd
    cA
    @2
    cP
    c.or
    cK
    @24
    dalem.j
    dalem.a
    @24
    eqid
    #
    llni2
    syl31anc
    3adant2
    @1
    @13
    @16
    @17
    @4
    cS
    wne
    @26
    @27
    wps
    wph
    @16
    @0
    @22
    3ad2ant3
    wph
    @0
    @17
    wps
    @23
    3ad2ant1
    @1
    cS
    @4
    @1
    cS
    cY
    c.le
    wbr
    #
    @4
    cY
    c.le
    wbr
    wn
    #
    cS
    @4
    wne
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
    dalem.l
    dalem.j
    dalem.a
    dalem23.z
    dalemsly
    3adant3
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
    dalem-ddly
    3ad2ant3
    cS
    @4
    cY
    c.le
    nbrne2
    syl2anc
    necomd
    cA
    @4
    cS
    c.or
    cK
    @24
    dalem.j
    dalem.a
    @28
    llni2
    syl31anc
    cA
    cO
    c.or
    cK
    c.an
    @24
    @3
    @5
    dalem.j
    dalem23.m
    dalem.a
    @28
    dalem23.o
    2llnmj
    syl3anc
    mpbird
    syl5eqel
end
