include "wa.mm"
include "chlt.mm"
include "wcel.mm"
include "cv.mm"
include "wne.mm"
include "co.mm"
include "clln.mm"
include "cfv.mm"
include "dalemkehl.mm"
include "adantr.mm"
include "dalemccea.mm"
include "adantl.mm"
include "dalemddea.mm"
include "dalemccnedd.mm"
include "eqid.mm"
include "llni2.mm"
include "syl31anc.mm"

theorem dalemcjden
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


  assert |- ( ( ph /\ ps ) -> ( c .\/ d ) e. ( LLines ` K ) )

  proof
    wph
    wps
    wa
    cK
    chlt
    wcel
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
    @1
    @3
    wne
    #
    @1
    @3
    c.or
    co
    cK
    clln
    cfv
    #
    wcel
    wph
    @0
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
    adantr
    wps
    @2
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
    wps
    @4
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
    adantl
    wps
    @5
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
    dalemccnedd
    adantl
    cA
    @1
    @3
    c.or
    cK
    @6
    dalem.j
    dalem.a
    @6
    eqid
    llni2
    syl31anc
end
