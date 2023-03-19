include "wceq.mm"
include "w3a.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "co.mm"
include "dalemddea.mm"
include "dalemccea.mm"
include "jca.mm"
include "3ad2ant3.mm"
include "dalem-ddly.mm"
include "simp2.mm"
include "breq2d.mm"
include "mtbid.mm"
include "dalemccnedd.mm"
include "dalem-ccly.mm"
include "dalemclccjdd.mm"
include "chlt.mm"
include "dalemkehl.mm"
include "3ad2ant1.mm"
include "hlatjcom.mm"
include "syl3anc.mm"
include "breqtrd.mm"
include "3jca.mm"

theorem dalemswapyzps
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
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
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


  assert |- ( ( ph /\ Y = Z /\ ps ) -> ( ( d e. A /\ c e. A ) /\ -. d .<_ Z /\ ( c =/= d /\ -. c .<_ Z /\ C .<_ ( d .\/ c ) ) ) )

  proof
    wph
    cY
    cZ
    wceq
    #
    wps
    w3a
    #
    vd
    cv
    #
    cA
    wcel
    #
    vc
    cv
    #
    cA
    wcel
    #
    wa
    #
    @2
    cZ
    c.le
    wbr
    #
    wn
    @4
    @2
    wne
    #
    @4
    cZ
    c.le
    wbr
    #
    wn
    #
    cC
    @2
    @4
    c.or
    co
    #
    c.le
    wbr
    #
    w3a
    wps
    wph
    @6
    @0
    wps
    @3
    @5
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
    #
    jca
    3ad2ant3
    @1
    @2
    cY
    c.le
    wbr
    #
    @7
    wps
    wph
    @15
    wn
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
    @1
    cY
    cZ
    @2
    c.le
    wph
    @0
    wps
    simp2
    #
    breq2d
    mtbid
    @1
    @8
    @10
    @12
    wps
    wph
    @8
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
    dalemccnedd
    3ad2ant3
    @1
    @4
    cY
    c.le
    wbr
    #
    @9
    wps
    wph
    @17
    wn
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
    @1
    cY
    cZ
    @4
    c.le
    @16
    breq2d
    mtbid
    @1
    cC
    @4
    @2
    c.or
    co
    #
    @11
    c.le
    wps
    wph
    cC
    @18
    c.le
    wbr
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
    @1
    cK
    chlt
    wcel
    #
    @5
    @3
    @18
    @11
    wceq
    wph
    @0
    @19
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
    @5
    @0
    @14
    3ad2ant3
    wps
    wph
    @3
    @0
    @13
    3ad2ant3
    cA
    c.or
    cK
    @4
    @2
    dalem.j
    dalem.a
    hlatjcom
    syl3anc
    breqtrd
    3jca
    3jca
end
