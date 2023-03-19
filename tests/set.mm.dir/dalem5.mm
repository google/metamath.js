include "cbs.mm"
include "cfv.mm"
include "co.mm"
include "eqid.mm"
include "dalemkelat.mm"
include "dalemueb.mm"
include "chlt.mm"
include "wcel.mm"
include "dalemkehl.mm"
include "dalemrea.mm"
include "dalemcea.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "clat.mm"
include "dalemyeb.mm"
include "dalemceb.mm"
include "latjcl.mm"
include "syl5eqel.mm"
include "wbr.mm"
include "dalemclrju.mm"
include "wne.mm"
include "wi.mm"
include "dalemuea.mm"
include "wn.mm"
include "dalempea.mm"
include "wa.mm"
include "w3a.mm"
include "simp313.mm"
include "sylbi.mm"
include "atnlej1.mm"
include "syl131anc.mm"
include "hlatexch1.mm"
include "mpd.mm"
include "dalempjqeb.mm"
include "dalemreb.mm"
include "latlej2.mm"
include "syl6breqr.mm"
include "latjlej1.mm"
include "syl13anc.mm"
include "lattrd.mm"

theorem dalem5
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
  let cW: class W
  let cY: class Y
  let cZ: class Z
  assume dalema.ph: |- ( ph <-> ( ( ( K e. HL /\ C e. ( Base ` K ) ) /\ ( P e. A /\ Q e. A /\ R e. A ) /\ ( S e. A /\ T e. A /\ U e. A ) ) /\ ( Y e. O /\ Z e. O ) /\ ( ( -. C .<_ ( P .\/ Q ) /\ -. C .<_ ( Q .\/ R ) /\ -. C .<_ ( R .\/ P ) ) /\ ( -. C .<_ ( S .\/ T ) /\ -. C .<_ ( T .\/ U ) /\ -. C .<_ ( U .\/ S ) ) /\ ( C .<_ ( P .\/ S ) /\ C .<_ ( Q .\/ T ) /\ C .<_ ( R .\/ U ) ) ) ) )
  assume dalemc.l: |- .<_ = ( le ` K )
  assume dalemc.j: |- .\/ = ( join ` K )
  assume dalemc.a: |- A = ( Atoms ` K )
  assume dalem5.o: |- O = ( LPlanes ` K )
  assume dalem5.y: |- Y = ( ( P .\/ Q ) .\/ R )
  assume dalem5.w: |- W = ( Y .\/ C )


  assert |- ( ph -> U .<_ W )

  proof
    wph
    cK
    cbs
    cfv
    #
    cK
    c.le
    cU
    cR
    cC
    c.or
    co
    #
    cW
    @0
    eqid
    #
    dalemc.l
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
    dalemc.a
    dalemueb
    wph
    cK
    chlt
    wcel
    #
    cR
    cA
    wcel
    #
    cC
    cA
    wcel
    #
    @1
    @0
    wcel
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
    dalemc.l
    dalemc.j
    dalemc.a
    dalem5.o
    dalem5.y
    dalemcea
    #
    cA
    @0
    c.or
    cK
    cR
    cC
    @2
    dalemc.j
    dalemc.a
    hlatjcl
    syl3anc
    wph
    cW
    cY
    cC
    c.or
    co
    #
    @0
    dalem5.w
    wph
    cK
    clat
    wcel
    #
    cY
    @0
    wcel
    #
    cC
    @0
    wcel
    #
    @10
    @0
    wcel
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
    dalem5.o
    dalemyeb
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
    dalemc.a
    dalemceb
    #
    @0
    c.or
    cK
    cY
    cC
    @2
    dalemc.j
    latjcl
    syl3anc
    syl5eqel
    wph
    cC
    cR
    cU
    c.or
    co
    c.le
    wbr
    #
    cU
    @1
    c.le
    wbr
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
    dalemclrju
    wph
    @4
    @6
    cU
    cA
    wcel
    #
    @5
    cC
    cR
    wne
    #
    @16
    @17
    wi
    @7
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
    dalemuea
    @8
    wph
    @4
    @6
    @5
    cP
    cA
    wcel
    #
    cC
    cR
    cP
    c.or
    co
    c.le
    wbr
    wn
    #
    @19
    @7
    @9
    @8
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
    wph
    @4
    @13
    wa
    @20
    cQ
    cA
    wcel
    @5
    w3a
    cS
    cA
    wcel
    cT
    cA
    wcel
    @18
    w3a
    w3a
    #
    cY
    cO
    wcel
    cZ
    cO
    wcel
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
    wn
    #
    cC
    cQ
    cR
    c.or
    co
    c.le
    wbr
    wn
    #
    @21
    w3a
    cC
    cS
    cT
    c.or
    co
    c.le
    wbr
    wn
    cC
    cT
    cU
    c.or
    co
    c.le
    wbr
    wn
    cC
    cU
    cS
    c.or
    co
    c.le
    wbr
    wn
    w3a
    #
    cC
    cP
    cS
    c.or
    co
    c.le
    wbr
    cC
    cQ
    cT
    c.or
    co
    c.le
    wbr
    @16
    w3a
    #
    w3a
    w3a
    @21
    dalema.ph
    @25
    @26
    @21
    @27
    @28
    @22
    @23
    simp313
    sylbi
    cA
    cC
    cR
    cP
    c.or
    cK
    c.le
    dalemc.l
    dalemc.j
    dalemc.a
    atnlej1
    syl131anc
    cA
    cC
    cU
    cR
    c.or
    cK
    c.le
    dalemc.l
    dalemc.j
    dalemc.a
    hlatexch1
    syl131anc
    mpd
    wph
    @1
    @10
    cW
    c.le
    wph
    cR
    cY
    c.le
    wbr
    #
    @1
    @10
    c.le
    wbr
    #
    wph
    cR
    @24
    cR
    c.or
    co
    #
    cY
    c.le
    wph
    @11
    @24
    @0
    wcel
    cR
    @0
    wcel
    #
    cR
    @31
    c.le
    wbr
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
    @0
    c.or
    cK
    c.le
    @24
    cR
    @2
    dalemc.l
    dalemc.j
    latlej2
    syl3anc
    dalem5.y
    syl6breqr
    wph
    @11
    @32
    @12
    @13
    @29
    @30
    wi
    @3
    @33
    @14
    @15
    @0
    c.or
    cK
    c.le
    cR
    cY
    cC
    @2
    dalemc.l
    dalemc.j
    latjlej1
    syl13anc
    mpd
    dalem5.w
    syl6breqr
    lattrd
end
