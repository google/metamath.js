include "co.mm"
include "clat.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "wbr.mm"
include "dalemkelat.mm"
include "dalempeb.mm"
include "chlt.mm"
include "dalemkehl.mm"
include "dalemqea.mm"
include "dalemrea.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "latlej1.mm"
include "wceq.mm"
include "dalempea.mm"
include "hlatjass.mm"
include "syl13anc.mm"
include "breqtrrd.mm"
include "syl6breqr.mm"

theorem dalemply
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
  assume dalempnes.o: |- O = ( LPlanes ` K )
  assume dalempnes.y: |- Y = ( ( P .\/ Q ) .\/ R )


  assert |- ( ph -> P .<_ Y )

  proof
    wph
    cP
    cP
    cQ
    c.or
    co
    cR
    c.or
    co
    #
    cY
    c.le
    wph
    cP
    cP
    cQ
    cR
    c.or
    co
    #
    c.or
    co
    #
    @0
    c.le
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
    @1
    @3
    wcel
    #
    cP
    @2
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
    cK
    chlt
    wcel
    #
    cQ
    cA
    wcel
    #
    cR
    cA
    wcel
    #
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
    dalemrea
    #
    cA
    @3
    c.or
    cK
    cQ
    cR
    @3
    eqid
    #
    dalemc.j
    dalemc.a
    hlatjcl
    syl3anc
    @3
    c.or
    cK
    c.le
    cP
    @1
    @11
    dalemc.l
    dalemc.j
    latlej1
    syl3anc
    wph
    @5
    cP
    cA
    wcel
    @6
    @7
    @0
    @2
    wceq
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
    @9
    @10
    cA
    cP
    cQ
    cR
    c.or
    cK
    dalemc.j
    dalemc.a
    hlatjass
    syl13anc
    breqtrrd
    dalempnes.y
    syl6breqr
end
