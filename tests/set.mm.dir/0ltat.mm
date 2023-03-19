include "cops.mm"
include "wcel.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "ccvr.mm"
include "wbr.mm"
include "simpl.mm"
include "eqid.mm"
include "op0cl.mm"
include "adantr.mm"
include "atbase.mm"
include "adantl.mm"
include "atcvr0.mm"
include "cvrlt.mm"
include "syl31anc.mm"

theorem 0ltat
  let cA: class A
  let cP: class P
  let c.lt: class .<
  let cK: class K
  let c.0: class .0.
  assume 0ltat.z: |- .0. = ( 0. ` K )
  assume 0ltat.s: |- .< = ( lt ` K )
  assume 0ltat.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. OP /\ P e. A ) -> .0. .< P )

  proof
    cK
    cops
    wcel
    #
    cP
    cA
    wcel
    #
    wa
    @0
    c.0
    cK
    cbs
    cfv
    #
    wcel
    #
    cP
    @2
    wcel
    #
    c.0
    cP
    cK
    ccvr
    cfv
    #
    wbr
    c.0
    cP
    c.lt
    wbr
    @0
    @1
    simpl
    @0
    @3
    @1
    @2
    cK
    c.0
    @2
    eqid
    #
    0ltat.z
    op0cl
    adantr
    @1
    @4
    @0
    cA
    @2
    cP
    cK
    @6
    0ltat.a
    atbase
    adantl
    cA
    @5
    cops
    cP
    cK
    c.0
    0ltat.z
    @5
    eqid
    #
    0ltat.a
    atcvr0
    cops
    @2
    @5
    c.lt
    cK
    c.0
    cP
    @6
    0ltat.s
    @7
    cvrlt
    syl31anc
end
