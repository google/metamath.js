include "chlt.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "wa.mm"
include "w3a.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "simp11l.mm"
include "sylbi.mm"

theorem dalemkehl
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


  assert |- ( ph -> K e. HL )

  proof
    wph
    cK
    chlt
    wcel
    #
    cC
    cK
    cbs
    cfv
    wcel
    #
    wa
    cP
    cA
    wcel
    cQ
    cA
    wcel
    cR
    cA
    wcel
    w3a
    #
    cS
    cA
    wcel
    cT
    cA
    wcel
    cU
    cA
    wcel
    w3a
    #
    w3a
    cY
    cO
    wcel
    cZ
    cO
    wcel
    wa
    #
    cC
    cP
    cQ
    c.or
    co
    c.le
    wbr
    wn
    cC
    cQ
    cR
    c.or
    co
    c.le
    wbr
    wn
    cC
    cR
    cP
    c.or
    co
    c.le
    wbr
    wn
    w3a
    cC
    cS
    cT
    c.or
    co
    c.le
    wbr
    wn
    cC
    cT
    cU
    c.or
    co
    c.le
    wbr
    wn
    cC
    cU
    cS
    c.or
    co
    c.le
    wbr
    wn
    w3a
    cC
    cP
    cS
    c.or
    co
    c.le
    wbr
    cC
    cQ
    cT
    c.or
    co
    c.le
    wbr
    cC
    cR
    cU
    c.or
    co
    c.le
    wbr
    w3a
    w3a
    #
    w3a
    @0
    dalema.ph
    @0
    @1
    @2
    @3
    @4
    @5
    simp11l
    sylbi
end
