include "wa.mm"
include "cv.mm"
include "wcel.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "w3a.mm"
include "dalemccea.mm"
include "dalemddea.mm"
include "jca.mm"
include "adantl.mm"
include "dalem-ccly.mm"
include "wb.mm"
include "dalemqrprot.mm"
include "syl6reqr.mm"
include "breq2d.mm"
include "adantr.mm"
include "mtbid.mm"
include "dalemccnedd.mm"
include "necomd.mm"
include "dalem-ddly.mm"
include "dalemclccjdd.mm"
include "3jca.mm"

theorem dalemrotps
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
  assume dalemrotps.y: |- Y = ( ( P .\/ Q ) .\/ R )


  assert |- ( ( ph /\ ps ) -> ( ( c e. A /\ d e. A ) /\ -. c .<_ ( ( Q .\/ R ) .\/ P ) /\ ( d =/= c /\ -. d .<_ ( ( Q .\/ R ) .\/ P ) /\ C .<_ ( c .\/ d ) ) ) )

  proof
    wph
    wps
    wa
    #
    vc
    cv
    #
    cA
    wcel
    #
    vd
    cv
    #
    cA
    wcel
    #
    wa
    #
    @1
    cQ
    cR
    c.or
    co
    cP
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    @3
    @1
    wne
    #
    @3
    @6
    c.le
    wbr
    #
    wn
    #
    cC
    @1
    @3
    c.or
    co
    c.le
    wbr
    #
    w3a
    wps
    @5
    wph
    wps
    @2
    @4
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
    jca
    adantl
    @0
    @1
    cY
    c.le
    wbr
    #
    @7
    wps
    @12
    wn
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
    dalem-ccly
    adantl
    wph
    @12
    @7
    wb
    wps
    wph
    cY
    @6
    @1
    c.le
    wph
    @6
    cP
    cQ
    c.or
    co
    cR
    c.or
    co
    cY
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
    dalem.j
    dalem.a
    dalemqrprot
    dalemrotps.y
    syl6reqr
    #
    breq2d
    adantr
    mtbid
    @0
    @8
    @10
    @11
    wps
    @8
    wph
    wps
    @1
    @3
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
    necomd
    adantl
    @0
    @3
    cY
    c.le
    wbr
    #
    @9
    wps
    @14
    wn
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
    dalem-ddly
    adantl
    wph
    @14
    @9
    wb
    wps
    wph
    cY
    @6
    @3
    c.le
    @13
    breq2d
    adantr
    mtbid
    wps
    @11
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
    dalemclccjdd
    adantl
    3jca
    3jca
end
