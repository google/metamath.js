include "chlt.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "wa.mm"
include "w3a.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "dalemrot.mm"
include "biid.mm"
include "eqid.mm"
include "dalemdea.mm"
include "syl.mm"

theorem dalemeea
  let wph: wff ph
  let cA: class A
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cE: class E
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cO: class O
  let cY: class Y
  let cZ: class Z
  assume dalema.ph: |- ( ph <-> ( ( ( K e. HL /\ C e. ( Base ` K ) ) /\ ( P e. A /\ Q e. A /\ R e. A ) /\ ( S e. A /\ T e. A /\ U e. A ) ) /\ ( Y e. O /\ Z e. O ) /\ ( ( -. C .<_ ( P .\/ Q ) /\ -. C .<_ ( Q .\/ R ) /\ -. C .<_ ( R .\/ P ) ) /\ ( -. C .<_ ( S .\/ T ) /\ -. C .<_ ( T .\/ U ) /\ -. C .<_ ( U .\/ S ) ) /\ ( C .<_ ( P .\/ S ) /\ C .<_ ( Q .\/ T ) /\ C .<_ ( R .\/ U ) ) ) ) )
  assume dalemc.l: |- .<_ = ( le ` K )
  assume dalemc.j: |- .\/ = ( join ` K )
  assume dalemc.a: |- A = ( Atoms ` K )
  assume dalemeea.m: |- ./\ = ( meet ` K )
  assume dalemeea.o: |- O = ( LPlanes ` K )
  assume dalemeea.y: |- Y = ( ( P .\/ Q ) .\/ R )
  assume dalemeea.z: |- Z = ( ( S .\/ T ) .\/ U )
  assume dalemeea.e: |- E = ( ( Q .\/ R ) ./\ ( T .\/ U ) )


  assert |- ( ph -> E e. A )

  proof
    wph
    cK
    chlt
    wcel
    cC
    cK
    cbs
    cfv
    wcel
    wa
    cQ
    cA
    wcel
    cR
    cA
    wcel
    cP
    cA
    wcel
    w3a
    cT
    cA
    wcel
    cU
    cA
    wcel
    cS
    cA
    wcel
    w3a
    w3a
    cQ
    cR
    c.or
    co
    #
    cP
    c.or
    co
    #
    cO
    wcel
    cT
    cU
    c.or
    co
    #
    cS
    c.or
    co
    #
    cO
    wcel
    wa
    cC
    @0
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
    cC
    cP
    cQ
    c.or
    co
    c.le
    wbr
    wn
    w3a
    cC
    @2
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
    cC
    cS
    cT
    c.or
    co
    c.le
    wbr
    wn
    w3a
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
    cC
    cP
    cS
    c.or
    co
    c.le
    wbr
    w3a
    w3a
    w3a
    #
    cE
    cA
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
    dalemc.l
    dalemc.j
    dalemc.a
    dalemeea.y
    dalemeea.z
    dalemrot
    @4
    cA
    cC
    cE
    cQ
    cR
    cP
    cT
    cU
    cS
    c.or
    cK
    c.le
    c.an
    cO
    @1
    @3
    @4
    biid
    dalemc.l
    dalemc.j
    dalemc.a
    dalemeea.m
    dalemeea.o
    @1
    eqid
    @3
    eqid
    dalemeea.e
    dalemdea
    syl
end
