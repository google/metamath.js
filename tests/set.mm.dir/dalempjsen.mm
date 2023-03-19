include "chlt.mm"
include "wcel.mm"
include "wne.mm"
include "co.mm"
include "clln.mm"
include "cfv.mm"
include "dalemkehl.mm"
include "dalempea.mm"
include "dalemsea.mm"
include "dalempnes.mm"
include "eqid.mm"
include "llni2.mm"
include "syl31anc.mm"

theorem dalempjsen
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


  assert |- ( ph -> ( P .\/ S ) e. ( LLines ` K ) )

  proof
    wph
    cK
    chlt
    wcel
    cP
    cA
    wcel
    cS
    cA
    wcel
    cP
    cS
    wne
    cP
    cS
    c.or
    co
    cK
    clln
    cfv
    #
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
    dalemsea
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
    dalempnes.o
    dalempnes.y
    dalempnes
    cA
    cP
    cS
    c.or
    cK
    @0
    dalemc.j
    dalemc.a
    @0
    eqid
    llni2
    syl31anc
end
