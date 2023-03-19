include "co.mm"
include "wbr.mm"
include "wne.mm"
include "dalemclpjs.mm"
include "wceq.mm"
include "wn.mm"
include "wa.mm"
include "dalem-clpjq.mm"
include "adantr.mm"
include "chlt.mm"
include "wcel.mm"
include "dalemkehl.mm"
include "dalempea.mm"
include "dalemsea.mm"
include "hlatlej1.mm"
include "syl3anc.mm"
include "dalemqea.mm"
include "dalemtea.mm"
include "simpr.mm"
include "breqtrrd.mm"
include "wb.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "dalemkelat.mm"
include "dalempeb.mm"
include "dalemqeb.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "dalemrea.mm"
include "dalemyeo.mm"
include "lplnri1.mm"
include "syl131anc.mm"
include "ps-1.mm"
include "syl132anc.mm"
include "mpbid.mm"
include "breq2d.mm"
include "mtbid.mm"
include "ex.mm"
include "necon2ad.mm"
include "mpd.mm"

theorem dalem1
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
  assume dalem1.o: |- O = ( LPlanes ` K )
  assume dalem1.y: |- Y = ( ( P .\/ Q ) .\/ R )


  assert |- ( ph -> ( P .\/ S ) =/= ( Q .\/ T ) )

  proof
    wph
    cC
    cP
    cS
    c.or
    co
    #
    c.le
    wbr
    #
    @0
    cQ
    cT
    c.or
    co
    #
    wne
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
    dalemclpjs
    wph
    @1
    @0
    @2
    wph
    @0
    @2
    wceq
    #
    @1
    wn
    wph
    @3
    wa
    #
    cC
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    @1
    wph
    @6
    wn
    @3
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
    dalem-clpjq
    adantr
    @4
    @5
    @0
    cC
    c.le
    @4
    @5
    @0
    c.le
    wbr
    #
    @5
    @0
    wceq
    #
    @4
    cP
    @0
    c.le
    wbr
    #
    cQ
    @0
    c.le
    wbr
    #
    @7
    wph
    @9
    @3
    wph
    cK
    chlt
    wcel
    #
    cP
    cA
    wcel
    #
    cS
    cA
    wcel
    #
    @9
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
    dalemsea
    #
    cA
    cP
    cS
    c.or
    cK
    c.le
    dalemc.l
    dalemc.j
    dalemc.a
    hlatlej1
    syl3anc
    adantr
    @4
    cQ
    @2
    @0
    c.le
    wph
    cQ
    @2
    c.le
    wbr
    #
    @3
    wph
    @11
    cQ
    cA
    wcel
    #
    cT
    cA
    wcel
    @17
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
    dalemtea
    cA
    cQ
    cT
    c.or
    cK
    c.le
    dalemc.l
    dalemc.j
    dalemc.a
    hlatlej1
    syl3anc
    adantr
    wph
    @3
    simpr
    breqtrrd
    wph
    @9
    @10
    wa
    @7
    wb
    #
    @3
    wph
    cK
    clat
    wcel
    cP
    cK
    cbs
    cfv
    #
    wcel
    cQ
    @21
    wcel
    @0
    @21
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
    dalema.ph
    dalemkelat
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
    dalema.ph
    dalemc.a
    dalemqeb
    wph
    @11
    @12
    @13
    @22
    @14
    @15
    @16
    cA
    @21
    c.or
    cK
    cP
    cS
    @21
    eqid
    #
    dalemc.j
    dalemc.a
    hlatjcl
    syl3anc
    @21
    c.or
    cK
    c.le
    cP
    cQ
    @0
    @23
    dalemc.l
    dalemc.j
    latjle12
    syl13anc
    adantr
    mpbi2and
    wph
    @7
    @8
    wb
    #
    @3
    wph
    @11
    @12
    @18
    cP
    cQ
    wne
    #
    @12
    @13
    @24
    @14
    @15
    @19
    wph
    @11
    @12
    @18
    cR
    cA
    wcel
    cY
    cO
    wcel
    @25
    @14
    @15
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
    dalemyeo
    cA
    cO
    cP
    cQ
    cR
    c.or
    cK
    cY
    dalemc.j
    dalemc.a
    dalem1.o
    dalem1.y
    lplnri1
    syl131anc
    @15
    @16
    cA
    cP
    cQ
    cP
    cS
    c.or
    cK
    c.le
    dalemc.l
    dalemc.j
    dalemc.a
    ps-1
    syl132anc
    adantr
    mpbid
    breq2d
    mtbid
    ex
    necon2ad
    mpd
end
