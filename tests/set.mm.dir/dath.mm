include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "cbs.mm"
include "cfv.mm"
include "eleq2i.mm"
include "anbi2i.mm"
include "3anbi1i.mm"
include "eqid.mm"
include "dalem63.mm"

theorem dath
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cE: class E
  let cF: class F
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cO: class O
  assume dath.b: |- B = ( Base ` K )
  assume dath.l: |- .<_ = ( le ` K )
  assume dath.j: |- .\/ = ( join ` K )
  assume dath.a: |- A = ( Atoms ` K )
  assume dath.m: |- ./\ = ( meet ` K )
  assume dath.o: |- O = ( LPlanes ` K )
  assume dath.d: |- D = ( ( P .\/ Q ) ./\ ( S .\/ T ) )
  assume dath.e: |- E = ( ( Q .\/ R ) ./\ ( T .\/ U ) )
  assume dath.f: |- F = ( ( R .\/ P ) ./\ ( U .\/ S ) )


  assert |- ( ( ( ( K e. HL /\ C e. B ) /\ ( P e. A /\ Q e. A /\ R e. A ) /\ ( S e. A /\ T e. A /\ U e. A ) ) /\ ( ( ( P .\/ Q ) .\/ R ) e. O /\ ( ( S .\/ T ) .\/ U ) e. O ) /\ ( ( -. C .<_ ( P .\/ Q ) /\ -. C .<_ ( Q .\/ R ) /\ -. C .<_ ( R .\/ P ) ) /\ ( -. C .<_ ( S .\/ T ) /\ -. C .<_ ( T .\/ U ) /\ -. C .<_ ( U .\/ S ) ) /\ ( C .<_ ( P .\/ S ) /\ C .<_ ( Q .\/ T ) /\ C .<_ ( R .\/ U ) ) ) ) -> F .<_ ( D .\/ E ) )

  proof
    cK
    chlt
    wcel
    #
    cC
    cB
    wcel
    #
    wa
    #
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
    #
    cP
    cQ
    c.or
    co
    #
    cR
    c.or
    co
    #
    cO
    wcel
    cS
    cT
    c.or
    co
    #
    cU
    c.or
    co
    #
    cO
    wcel
    wa
    #
    cC
    @6
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
    @8
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
    cA
    cC
    cD
    cP
    cQ
    cR
    cS
    cT
    cU
    cE
    cF
    c.or
    cK
    c.le
    c.an
    cO
    @7
    @9
    @5
    @0
    cC
    cK
    cbs
    cfv
    #
    wcel
    #
    wa
    #
    @3
    @4
    w3a
    @10
    @11
    @2
    @14
    @3
    @4
    @1
    @13
    @0
    cB
    @12
    cC
    dath.b
    eleq2i
    anbi2i
    3anbi1i
    3anbi1i
    dath.l
    dath.j
    dath.a
    dath.m
    dath.o
    @7
    eqid
    @9
    eqid
    dath.d
    dath.e
    dath.f
    dalem63
end
