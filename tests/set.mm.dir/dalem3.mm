include "wne.mm"
include "wa.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "chlt.mm"
include "wcel.mm"
include "dalemkehl.mm"
include "dalempea.mm"
include "dalemqea.mm"
include "dalemrea.mm"
include "dalemyeo.mm"
include "lplnric.mm"
include "syl131anc.mm"
include "adantr.mm"
include "wceq.mm"
include "wi.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "dalemkelat.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "dalemtjueb.mm"
include "latmle1.mm"
include "syl5eqbr.mm"
include "breq1.mm"
include "syl5ibrcom.mm"
include "dalemdea.mm"
include "simpr.mm"
include "hlatexch1.mm"
include "hlatlej2.mm"
include "dalempjqeb.mm"
include "dalemsjteb.mm"
include "wb.mm"
include "dalemqeb.mm"
include "atbase.mm"
include "syl.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "dalemreb.mm"
include "lattr.mm"
include "mpan2d.mm"
include "3syld.mm"
include "necon3bd.mm"
include "mpd.mm"

theorem dalem3
  let wph: wff ph
  let cA: class A
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cE: class E
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cO: class O
  let cY: class Y
  let cZ: class Z
  assume dalema.ph: |- ( ph <-> ( ( ( K e. HL /\ C e. ( Base ` K ) ) /\ ( P e. A /\ Q e. A /\ R e. A ) /\ ( S e. A /\ T e. A /\ U e. A ) ) /\ ( Y e. O /\ Z e. O ) /\ ( ( -. C .<_ ( P .\/ Q ) /\ -. C .<_ ( Q .\/ R ) /\ -. C .<_ ( R .\/ P ) ) /\ ( -. C .<_ ( S .\/ T ) /\ -. C .<_ ( T .\/ U ) /\ -. C .<_ ( U .\/ S ) ) /\ ( C .<_ ( P .\/ S ) /\ C .<_ ( Q .\/ T ) /\ C .<_ ( R .\/ U ) ) ) ) )
  assume dalemc.l: |- .<_ = ( le ` K )
  assume dalemc.j: |- .\/ = ( join ` K )
  assume dalemc.a: |- A = ( Atoms ` K )
  assume dalem3.m: |- ./\ = ( meet ` K )
  assume dalem3.o: |- O = ( LPlanes ` K )
  assume dalem3.y: |- Y = ( ( P .\/ Q ) .\/ R )
  assume dalem3.z: |- Z = ( ( S .\/ T ) .\/ U )
  assume dalem3.d: |- D = ( ( P .\/ Q ) ./\ ( S .\/ T ) )
  assume dalem3.e: |- E = ( ( Q .\/ R ) ./\ ( T .\/ U ) )


  assert |- ( ( ph /\ D =/= Q ) -> D =/= E )

  proof
    wph
    cD
    cQ
    wne
    #
    wa
    #
    cR
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    #
    cD
    cE
    wne
    wph
    @4
    @0
    wph
    cK
    chlt
    wcel
    #
    cP
    cA
    wcel
    #
    cQ
    cA
    wcel
    #
    cR
    cA
    wcel
    #
    cY
    cO
    wcel
    @4
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
    dalema.ph
    dalemkehl
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
    dalema.ph
    dalempea
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
    dalema.ph
    dalemqea
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
    dalema.ph
    dalemrea
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
    dalema.ph
    dalemyeo
    cA
    cO
    cP
    cQ
    cR
    c.or
    cK
    c.le
    cY
    dalemc.l
    dalemc.j
    dalemc.a
    dalem3.o
    dalem3.y
    lplnric
    syl131anc
    adantr
    @1
    @3
    cD
    cE
    @1
    cD
    cE
    wceq
    #
    cD
    cQ
    cR
    c.or
    co
    #
    c.le
    wbr
    #
    cR
    cQ
    cD
    c.or
    co
    #
    c.le
    wbr
    #
    @3
    wph
    @13
    @15
    wi
    @0
    wph
    @15
    @13
    cE
    @14
    c.le
    wbr
    wph
    cE
    @14
    cT
    cU
    c.or
    co
    #
    c.an
    co
    #
    @14
    c.le
    dalem3.e
    wph
    cK
    clat
    wcel
    #
    @14
    cK
    cbs
    cfv
    #
    wcel
    #
    @18
    @21
    wcel
    @19
    @14
    c.le
    wbr
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
    dalema.ph
    dalemkelat
    #
    wph
    @5
    @7
    @8
    @22
    @9
    @11
    @12
    cA
    @21
    c.or
    cK
    cQ
    cR
    @21
    eqid
    #
    dalemc.j
    dalemc.a
    hlatjcl
    syl3anc
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
    dalema.ph
    dalemc.j
    dalemc.a
    dalemtjueb
    @21
    cK
    c.le
    c.an
    @14
    @18
    @24
    dalemc.l
    dalem3.m
    latmle1
    syl3anc
    syl5eqbr
    cD
    cE
    @14
    c.le
    breq1
    syl5ibrcom
    adantr
    @1
    @5
    cD
    cA
    wcel
    #
    @8
    @7
    @0
    @15
    @17
    wi
    wph
    @5
    @0
    @9
    adantr
    wph
    @25
    @0
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
    dalema.ph
    dalemc.l
    dalemc.j
    dalemc.a
    dalem3.m
    dalem3.o
    dalem3.y
    dalem3.z
    dalem3.d
    dalemdea
    #
    adantr
    wph
    @8
    @0
    @12
    adantr
    wph
    @7
    @0
    @11
    adantr
    wph
    @0
    simpr
    cA
    cD
    cR
    cQ
    c.or
    cK
    c.le
    dalemc.l
    dalemc.j
    dalemc.a
    hlatexch1
    syl131anc
    wph
    @17
    @3
    wi
    @0
    wph
    @17
    @16
    @2
    c.le
    wbr
    #
    @3
    wph
    cQ
    @2
    c.le
    wbr
    #
    cD
    @2
    c.le
    wbr
    #
    @27
    wph
    @5
    @6
    @7
    @28
    @9
    @10
    @11
    cA
    cP
    cQ
    c.or
    cK
    c.le
    dalemc.l
    dalemc.j
    dalemc.a
    hlatlej2
    syl3anc
    wph
    cD
    @2
    cS
    cT
    c.or
    co
    #
    c.an
    co
    #
    @2
    c.le
    dalem3.d
    wph
    @20
    @2
    @21
    wcel
    #
    @30
    @21
    wcel
    @31
    @2
    c.le
    wbr
    @23
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
    dalema.ph
    dalemc.j
    dalemc.a
    dalempjqeb
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
    dalema.ph
    dalemc.j
    dalemc.a
    dalemsjteb
    @21
    cK
    c.le
    c.an
    @2
    @30
    @24
    dalemc.l
    dalem3.m
    latmle1
    syl3anc
    syl5eqbr
    wph
    @20
    cQ
    @21
    wcel
    cD
    @21
    wcel
    #
    @32
    @28
    @29
    wa
    @27
    wb
    @23
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
    dalema.ph
    dalemc.a
    dalemqeb
    wph
    @25
    @34
    @26
    cA
    @21
    cD
    cK
    @24
    dalemc.a
    atbase
    syl
    @33
    @21
    c.or
    cK
    c.le
    cQ
    cD
    @2
    @24
    dalemc.l
    dalemc.j
    latjle12
    syl13anc
    mpbi2and
    wph
    @20
    cR
    @21
    wcel
    @16
    @21
    wcel
    #
    @32
    @17
    @27
    wa
    @3
    wi
    @23
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
    dalema.ph
    dalemc.a
    dalemreb
    wph
    @5
    @7
    @25
    @35
    @9
    @11
    @26
    cA
    @21
    c.or
    cK
    cQ
    cD
    @24
    dalemc.j
    dalemc.a
    hlatjcl
    syl3anc
    @33
    @21
    cK
    c.le
    cR
    @16
    @2
    @24
    dalemc.l
    lattr
    syl13anc
    mpan2d
    adantr
    3syld
    necon3bd
    mpd
end
