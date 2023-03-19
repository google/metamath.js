include "wceq.mm"
include "wa.mm"
include "co.mm"
include "wbr.mm"
include "dalemclrju.mm"
include "adantr.mm"
include "clat.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "dalemkelat.mm"
include "dalempjqeb.mm"
include "dalemreb.mm"
include "eqid.mm"
include "latlej2.mm"
include "syl3anc.mm"
include "syl6breqr.mm"
include "dalemsjteb.mm"
include "dalemueb.mm"
include "simpr.mm"
include "breqtrrd.mm"
include "wb.mm"
include "dalemyeb.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "wi.mm"
include "dalemceb.mm"
include "chlt.mm"
include "dalemkehl.mm"
include "dalemrea.mm"
include "dalemuea.mm"
include "hlatjcl.mm"
include "lattr.mm"
include "mp2and.mm"

theorem dalem17
  let wph: wff ph
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
  let cO: class O
  let cY: class Y
  let cZ: class Z
  assume dalema.ph: |- ( ph <-> ( ( ( K e. HL /\ C e. ( Base ` K ) ) /\ ( P e. A /\ Q e. A /\ R e. A ) /\ ( S e. A /\ T e. A /\ U e. A ) ) /\ ( Y e. O /\ Z e. O ) /\ ( ( -. C .<_ ( P .\/ Q ) /\ -. C .<_ ( Q .\/ R ) /\ -. C .<_ ( R .\/ P ) ) /\ ( -. C .<_ ( S .\/ T ) /\ -. C .<_ ( T .\/ U ) /\ -. C .<_ ( U .\/ S ) ) /\ ( C .<_ ( P .\/ S ) /\ C .<_ ( Q .\/ T ) /\ C .<_ ( R .\/ U ) ) ) ) )
  assume dalemc.l: |- .<_ = ( le ` K )
  assume dalemc.j: |- .\/ = ( join ` K )
  assume dalemc.a: |- A = ( Atoms ` K )
  assume dalem17.o: |- O = ( LPlanes ` K )
  assume dalem17.y: |- Y = ( ( P .\/ Q ) .\/ R )
  assume dalem17.z: |- Z = ( ( S .\/ T ) .\/ U )


  assert |- ( ( ph /\ Y = Z ) -> C .<_ Y )

  proof
    wph
    cY
    cZ
    wceq
    #
    wa
    #
    cC
    cR
    cU
    c.or
    co
    #
    c.le
    wbr
    #
    @2
    cY
    c.le
    wbr
    #
    cC
    cY
    c.le
    wbr
    #
    wph
    @3
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
    dalemclrju
    adantr
    @1
    cR
    cY
    c.le
    wbr
    #
    cU
    cY
    c.le
    wbr
    #
    @4
    wph
    @6
    @0
    wph
    cR
    cP
    cQ
    c.or
    co
    #
    cR
    c.or
    co
    #
    cY
    c.le
    wph
    cK
    clat
    wcel
    #
    @8
    cK
    cbs
    cfv
    #
    wcel
    cR
    @11
    wcel
    #
    cR
    @9
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
    #
    @11
    c.or
    cK
    c.le
    @8
    cR
    @11
    eqid
    #
    dalemc.l
    dalemc.j
    latlej2
    syl3anc
    dalem17.y
    syl6breqr
    adantr
    @1
    cU
    cZ
    cY
    c.le
    wph
    cU
    cZ
    c.le
    wbr
    @0
    wph
    cU
    cS
    cT
    c.or
    co
    #
    cU
    c.or
    co
    #
    cZ
    c.le
    wph
    @10
    @16
    @11
    wcel
    cU
    @11
    wcel
    #
    cU
    @17
    c.le
    wbr
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
    dalema.ph
    dalemc.j
    dalemc.a
    dalemsjteb
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
    dalemueb
    #
    @11
    c.or
    cK
    c.le
    @16
    cU
    @15
    dalemc.l
    dalemc.j
    latlej2
    syl3anc
    dalem17.z
    syl6breqr
    adantr
    wph
    @0
    simpr
    breqtrrd
    wph
    @6
    @7
    wa
    @4
    wb
    #
    @0
    wph
    @10
    @12
    @18
    cY
    @11
    wcel
    #
    @20
    @13
    @14
    @19
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
    dalem17.o
    dalemyeb
    #
    @11
    c.or
    cK
    c.le
    cR
    cU
    cY
    @15
    dalemc.l
    dalemc.j
    latjle12
    syl13anc
    adantr
    mpbi2and
    wph
    @3
    @4
    wa
    @5
    wi
    #
    @0
    wph
    @10
    cC
    @11
    wcel
    @2
    @11
    wcel
    #
    @21
    @23
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
    dalema.ph
    dalemc.a
    dalemceb
    wph
    cK
    chlt
    wcel
    cR
    cA
    wcel
    cU
    cA
    wcel
    @24
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
    dalemuea
    cA
    @11
    c.or
    cK
    cR
    cU
    @15
    dalemc.j
    dalemc.a
    hlatjcl
    syl3anc
    @22
    @11
    cK
    c.le
    cC
    @2
    cY
    @15
    dalemc.l
    lattr
    syl13anc
    adantr
    mp2and
end
