include "cv.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "wrex.mm"
include "chlt.mm"
include "wcel.mm"
include "dalemkehl.mm"
include "dalempea.mm"
include "dalemqea.mm"
include "dalemrea.mm"
include "3dim3.mm"
include "syl13anc.mm"
include "breq2i.mm"
include "notbii.mm"
include "rexbii.mm"
include "sylibr.mm"

theorem dalem18
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
  let vc: setvar c
  assume dalema.ph: |- ( ph <-> ( ( ( K e. HL /\ C e. ( Base ` K ) ) /\ ( P e. A /\ Q e. A /\ R e. A ) /\ ( S e. A /\ T e. A /\ U e. A ) ) /\ ( Y e. O /\ Z e. O ) /\ ( ( -. C .<_ ( P .\/ Q ) /\ -. C .<_ ( Q .\/ R ) /\ -. C .<_ ( R .\/ P ) ) /\ ( -. C .<_ ( S .\/ T ) /\ -. C .<_ ( T .\/ U ) /\ -. C .<_ ( U .\/ S ) ) /\ ( C .<_ ( P .\/ S ) /\ C .<_ ( Q .\/ T ) /\ C .<_ ( R .\/ U ) ) ) ) )
  assume dalemc.l: |- .<_ = ( le ` K )
  assume dalemc.j: |- .\/ = ( join ` K )
  assume dalemc.a: |- A = ( Atoms ` K )
  assume dalem18.y: |- Y = ( ( P .\/ Q ) .\/ R )

  disjoint A c
  disjoint .\/ c
  disjoint .<_ c
  disjoint P c
  disjoint Q c
  disjoint R c
  assert |- ( ph -> E. c e. A -. c .<_ Y )

  proof
    wph
    vc
    cv
    #
    cP
    cQ
    c.or
    co
    cR
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    #
    vc
    cA
    wrex
    #
    @0
    cY
    c.le
    wbr
    #
    wn
    #
    vc
    cA
    wrex
    wph
    cK
    chlt
    wcel
    cP
    cA
    wcel
    cQ
    cA
    wcel
    cR
    cA
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
    cA
    cP
    cQ
    cR
    c.or
    cK
    c.le
    vc
    dalemc.j
    dalemc.l
    dalemc.a
    3dim3
    syl13anc
    @6
    @3
    vc
    cA
    @5
    @2
    cY
    @1
    @0
    c.le
    dalem18.y
    breq2i
    notbii
    rexbii
    sylibr
end
