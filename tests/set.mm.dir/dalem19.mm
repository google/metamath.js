include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "wcel.mm"
include "wbr.mm"
include "wn.mm"
include "chlt.mm"
include "cbs.mm"
include "cfv.mm"
include "wne.mm"
include "co.mm"
include "w3a.mm"
include "wrex.mm"
include "dalemkehl.mm"
include "ad3antrrr.mm"
include "dalemcea.mm"
include "simplr.mm"
include "dalemyeb.mm"
include "dalem17.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "eqid.mm"
include "atbtwnex.mm"
include "syl33anc.mm"

theorem dalem19
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
  let vd: setvar d
  assume dalema.ph: |- ( ph <-> ( ( ( K e. HL /\ C e. ( Base ` K ) ) /\ ( P e. A /\ Q e. A /\ R e. A ) /\ ( S e. A /\ T e. A /\ U e. A ) ) /\ ( Y e. O /\ Z e. O ) /\ ( ( -. C .<_ ( P .\/ Q ) /\ -. C .<_ ( Q .\/ R ) /\ -. C .<_ ( R .\/ P ) ) /\ ( -. C .<_ ( S .\/ T ) /\ -. C .<_ ( T .\/ U ) /\ -. C .<_ ( U .\/ S ) ) /\ ( C .<_ ( P .\/ S ) /\ C .<_ ( Q .\/ T ) /\ C .<_ ( R .\/ U ) ) ) ) )
  assume dalemc.l: |- .<_ = ( le ` K )
  assume dalemc.j: |- .\/ = ( join ` K )
  assume dalemc.a: |- A = ( Atoms ` K )
  assume dalem19.o: |- O = ( LPlanes ` K )
  assume dalem19.y: |- Y = ( ( P .\/ Q ) .\/ R )
  assume dalem19.z: |- Z = ( ( S .\/ T ) .\/ U )

  disjoint c d
  disjoint A d
  disjoint C d
  disjoint K d
  disjoint .<_ d
  disjoint Y d
  assert |- ( ( ( ( ph /\ Y = Z ) /\ c e. A ) /\ -. c .<_ Y ) -> E. d e. A ( d =/= c /\ -. d .<_ Y /\ C .<_ ( c .\/ d ) ) )

  proof
    wph
    cY
    cZ
    wceq
    #
    wa
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
    cY
    c.le
    wbr
    wn
    #
    wa
    cK
    chlt
    wcel
    #
    cC
    cA
    wcel
    #
    @3
    cY
    cK
    cbs
    cfv
    #
    wcel
    #
    cC
    cY
    c.le
    wbr
    #
    @5
    vd
    cv
    #
    @2
    wne
    @11
    cY
    c.le
    wbr
    wn
    cC
    @2
    @11
    c.or
    co
    c.le
    wbr
    w3a
    vd
    cA
    wrex
    wph
    @6
    @0
    @3
    @5
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
    ad3antrrr
    wph
    @7
    @0
    @3
    @5
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
    dalem19.o
    dalem19.y
    dalemcea
    ad3antrrr
    @1
    @3
    @5
    simplr
    wph
    @9
    @0
    @3
    @5
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
    dalem19.o
    dalemyeb
    ad3antrrr
    @1
    @10
    @3
    @5
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
    dalem19.o
    dalem19.y
    dalem19.z
    dalem17
    ad2antrr
    @4
    @5
    simpr
    cA
    @8
    cC
    @2
    c.or
    cK
    c.le
    cY
    vd
    @8
    eqid
    dalemc.l
    dalemc.j
    dalemc.a
    atbtwnex
    syl33anc
end
