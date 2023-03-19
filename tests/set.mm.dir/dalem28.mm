include "wceq.mm"
include "w3a.mm"
include "cv.mm"
include "co.mm"
include "wbr.mm"
include "dalem27.mm"
include "chlt.mm"
include "wcel.mm"
include "wne.mm"
include "wi.mm"
include "dalemkehl.mm"
include "3ad2ant1.mm"
include "dalemccea.mm"
include "3ad2ant3.mm"
include "dalempea.mm"
include "dalem23.mm"
include "dalem25.mm"
include "hlatexch1.mm"
include "syl131anc.mm"
include "mpd.mm"

theorem dalem28
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


  assert |- ( ( ph /\ Y = Z /\ ps ) -> P .<_ ( G .\/ c ) )

  proof
    wph
    cY
    cZ
    wceq
    #
    wps
    w3a
    #
    vc
    cv
    #
    cG
    cP
    c.or
    co
    c.le
    wbr
    #
    cP
    cG
    @2
    c.or
    co
    c.le
    wbr
    #
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
    dalem27
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
    cG
    cA
    wcel
    @2
    cG
    wne
    @3
    @4
    wi
    wph
    @0
    @5
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
    wps
    wph
    @6
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
    wph
    @0
    @7
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
    dalem25
    cA
    @2
    cP
    cG
    c.or
    cK
    c.le
    dalem.l
    dalem.j
    dalem.a
    hlatexch1
    syl131anc
    mpd
end
