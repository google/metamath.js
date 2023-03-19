include "chlt.mm"
include "wcel.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "dalemkehl.mm"
include "dalemtea.mm"
include "dalemuea.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "syl3anc.mm"

theorem dalemtjueb
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
  assume dalemb.j: |- .\/ = ( join ` K )
  assume dalemb.a: |- A = ( Atoms ` K )


  assert |- ( ph -> ( T .\/ U ) e. ( Base ` K ) )

  proof
    wph
    cK
    chlt
    wcel
    cT
    cA
    wcel
    cU
    cA
    wcel
    cT
    cU
    c.or
    co
    cK
    cbs
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
    dalemtea
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
    cA
    @0
    c.or
    cK
    cT
    cU
    @0
    eqid
    dalemb.j
    dalemb.a
    hlatjcl
    syl3anc
end
