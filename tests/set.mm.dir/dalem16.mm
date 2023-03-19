include "wne.mm"
include "wa.mm"
include "co.mm"
include "wbr.mm"
include "eqid.mm"
include "dalem12.mm"
include "adantr.mm"
include "wceq.mm"
include "dalem10.mm"
include "dalem11.mm"
include "clat.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "wb.mm"
include "dalemkelat.mm"
include "dalemdea.mm"
include "atbase.mm"
include "syl.mm"
include "dalemeea.mm"
include "dalemyeb.mm"
include "dalemzeo.mm"
include "lplnbase.mm"
include "latmcl.mm"
include "syl3anc.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "chlt.mm"
include "clln.mm"
include "dalemkehl.mm"
include "dalemdnee.mm"
include "llni2.mm"
include "syl31anc.mm"
include "dalem15.mm"
include "llncmp.mm"
include "mpbid.mm"
include "breqtrrd.mm"

theorem dalem16
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
  let cF: class F
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
  assume dalem16.m: |- ./\ = ( meet ` K )
  assume dalem16.o: |- O = ( LPlanes ` K )
  assume dalem16.y: |- Y = ( ( P .\/ Q ) .\/ R )
  assume dalem16.z: |- Z = ( ( S .\/ T ) .\/ U )
  assume dalem16.d: |- D = ( ( P .\/ Q ) ./\ ( S .\/ T ) )
  assume dalem16.e: |- E = ( ( Q .\/ R ) ./\ ( T .\/ U ) )
  assume dalem16.f: |- F = ( ( R .\/ P ) ./\ ( U .\/ S ) )


  assert |- ( ( ph /\ Y =/= Z ) -> F .<_ ( D .\/ E ) )

  proof
    wph
    cY
    cZ
    wne
    #
    wa
    #
    cF
    cY
    cZ
    c.an
    co
    #
    cD
    cE
    c.or
    co
    #
    c.le
    wph
    cF
    @2
    c.le
    wbr
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
    cF
    c.or
    cK
    c.le
    c.an
    cO
    @2
    cY
    cZ
    dalema.ph
    dalemc.l
    dalemc.j
    dalemc.a
    dalem16.m
    dalem16.o
    dalem16.y
    dalem16.z
    @2
    eqid
    #
    dalem16.f
    dalem12
    adantr
    @1
    @3
    @2
    c.le
    wbr
    #
    @3
    @2
    wceq
    #
    wph
    @5
    @0
    wph
    cD
    @2
    c.le
    wbr
    #
    cE
    @2
    c.le
    wbr
    #
    @5
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
    @2
    cY
    cZ
    dalema.ph
    dalemc.l
    dalemc.j
    dalemc.a
    dalem16.m
    dalem16.o
    dalem16.y
    dalem16.z
    @4
    dalem16.d
    dalem10
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
    @2
    cY
    cZ
    dalema.ph
    dalemc.l
    dalemc.j
    dalemc.a
    dalem16.m
    dalem16.o
    dalem16.y
    dalem16.z
    @4
    dalem16.e
    dalem11
    wph
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
    @10
    wcel
    #
    @2
    @10
    wcel
    #
    @7
    @8
    wa
    @5
    wb
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
    cD
    cA
    wcel
    #
    @11
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
    dalem16.m
    dalem16.o
    dalem16.y
    dalem16.z
    dalem16.d
    dalemdea
    #
    cA
    @10
    cD
    cK
    @10
    eqid
    #
    dalemc.a
    atbase
    syl
    wph
    cE
    cA
    wcel
    #
    @12
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
    dalema.ph
    dalemc.l
    dalemc.j
    dalemc.a
    dalem16.m
    dalem16.o
    dalem16.y
    dalem16.z
    dalem16.e
    dalemeea
    #
    cA
    @10
    cE
    cK
    @17
    dalemc.a
    atbase
    syl
    wph
    @9
    cY
    @10
    wcel
    cZ
    @10
    wcel
    #
    @13
    @14
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
    dalem16.o
    dalemyeb
    wph
    cZ
    cO
    wcel
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
    dalema.ph
    dalemzeo
    @10
    cO
    cK
    cZ
    @17
    dalem16.o
    lplnbase
    syl
    @10
    cK
    c.an
    cY
    cZ
    @17
    dalem16.m
    latmcl
    syl3anc
    @10
    c.or
    cK
    c.le
    cD
    cE
    @2
    @17
    dalemc.l
    dalemc.j
    latjle12
    syl13anc
    mpbi2and
    adantr
    @1
    cK
    chlt
    wcel
    #
    @3
    cK
    clln
    cfv
    #
    wcel
    #
    @2
    @22
    wcel
    @5
    @6
    wb
    wph
    @21
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
    dalema.ph
    dalemkehl
    #
    adantr
    wph
    @23
    @0
    wph
    @21
    @15
    @18
    cD
    cE
    wne
    @23
    @24
    @16
    @19
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
    dalema.ph
    dalemc.l
    dalemc.j
    dalemc.a
    dalem16.m
    dalem16.o
    dalem16.y
    dalem16.z
    dalem16.d
    dalem16.e
    dalemdnee
    cA
    cD
    cE
    c.or
    cK
    @22
    dalemc.j
    dalemc.a
    @22
    eqid
    #
    llni2
    syl31anc
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
    c.an
    @22
    cO
    @2
    cY
    cZ
    dalema.ph
    dalemc.l
    dalemc.j
    dalemc.a
    dalem16.m
    @25
    dalem16.o
    dalem16.y
    dalem16.z
    @4
    dalem15
    cK
    c.le
    @22
    @3
    @2
    dalemc.l
    @25
    llncmp
    syl3anc
    mpbid
    breqtrrd
end
