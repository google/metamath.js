include "wceq.mm"
include "w3a.mm"
include "cv.mm"
include "co.mm"
include "wbr.mm"
include "clat.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "dalemkelat.mm"
include "3ad2ant1.mm"
include "chlt.mm"
include "dalemkehl.mm"
include "dalemccea.mm"
include "3ad2ant3.mm"
include "dalempea.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "dalemddea.mm"
include "dalemsea.mm"
include "latmle1.mm"
include "syl5eqbr.mm"
include "wne.mm"
include "wi.mm"
include "dalem23.mm"
include "wn.mm"
include "dalemply.mm"
include "dalem24.mm"
include "wa.mm"
include "nbrne2.mm"
include "necomd.mm"
include "syl2anc.mm"
include "hlatexch2.mm"
include "syl131anc.mm"
include "mpd.mm"

theorem dalem27
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


  assert |- ( ( ph /\ Y = Z /\ ps ) -> c .<_ ( G .\/ P ) )

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
    c.le
    wbr
    #
    @2
    cG
    cP
    c.or
    co
    c.le
    wbr
    #
    @1
    cG
    @3
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
    @3
    c.le
    dalem23.g
    @1
    cK
    clat
    wcel
    #
    @3
    cK
    cbs
    cfv
    #
    wcel
    #
    @7
    @10
    wcel
    #
    @8
    @3
    c.le
    wbr
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
    dalemkelat
    3ad2ant1
    @1
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
    @11
    wph
    @0
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
    3ad2ant1
    #
    wps
    wph
    @14
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
    3ad2ant1
    #
    cA
    @10
    c.or
    cK
    @2
    cP
    @10
    eqid
    #
    dalem.j
    dalem.a
    hlatjcl
    syl3anc
    @1
    @13
    @6
    cA
    wcel
    #
    cS
    cA
    wcel
    #
    @12
    @16
    wps
    wph
    @20
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
    wph
    @0
    @21
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
    3ad2ant1
    cA
    @10
    c.or
    cK
    @6
    cS
    @19
    dalem.j
    dalem.a
    hlatjcl
    syl3anc
    @10
    cK
    c.le
    c.an
    @3
    @7
    @19
    dalem.l
    dalem23.m
    latmle1
    syl3anc
    syl5eqbr
    @1
    @13
    cG
    cA
    wcel
    @14
    @15
    cG
    cP
    wne
    #
    @4
    @5
    wi
    @16
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
    @17
    @18
    @1
    cP
    cY
    c.le
    wbr
    #
    cG
    cY
    c.le
    wbr
    wn
    #
    @22
    wph
    @0
    @23
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
    dalem24
    @23
    @24
    wa
    cP
    cG
    cP
    cG
    cY
    c.le
    nbrne2
    necomd
    syl2anc
    cA
    cG
    @2
    cP
    c.or
    cK
    c.le
    dalem.l
    dalem.j
    dalem.a
    hlatexch2
    syl131anc
    mpd
end
