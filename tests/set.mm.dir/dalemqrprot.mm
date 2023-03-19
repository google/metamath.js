include "chlt.mm"
include "wcel.mm"
include "co.mm"
include "wceq.mm"
include "dalemkehl.mm"
include "dalemqea.mm"
include "dalemrea.mm"
include "dalempea.mm"
include "hlatjrot.mm"
include "syl13anc.mm"

theorem dalemqrprot
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


  assert |- ( ph -> ( ( Q .\/ R ) .\/ P ) = ( ( P .\/ Q ) .\/ R ) )

  proof
    wph
    cK
    chlt
    wcel
    cQ
    cA
    wcel
    cR
    cA
    wcel
    cP
    cA
    wcel
    cQ
    cR
    c.or
    co
    cP
    c.or
    co
    cP
    cQ
    c.or
    co
    cR
    c.or
    co
    wceq
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
    cA
    cQ
    cR
    cP
    c.or
    cK
    dalemb.j
    dalemb.a
    hlatjrot
    syl13anc
end
