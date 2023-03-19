include "cal.mm"
include "wcel.mm"
include "wa.mm"
include "cpo.mm"
include "cbs.mm"
include "cfv.mm"
include "ccvr.mm"
include "wbr.mm"
include "wn.mm"
include "atlpos.mm"
include "adantr.mm"
include "eqid.mm"
include "atl0cl.mm"
include "atbase.mm"
include "adantl.mm"
include "atcvr0.mm"
include "cvrnle.mm"
include "syl31anc.mm"

theorem atnle0
  let cA: class A
  let cP: class P
  let cK: class K
  let c.le: class .<_
  let c.0: class .0.
  assume atnle0.l: |- .<_ = ( le ` K )
  assume atnle0.z: |- .0. = ( 0. ` K )
  assume atnle0.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. AtLat /\ P e. A ) -> -. P .<_ .0. )

  proof
    cK
    cal
    wcel
    #
    cP
    cA
    wcel
    #
    wa
    cK
    cpo
    wcel
    #
    c.0
    cK
    cbs
    cfv
    #
    wcel
    #
    cP
    @3
    wcel
    #
    c.0
    cP
    cK
    ccvr
    cfv
    #
    wbr
    cP
    c.0
    c.le
    wbr
    wn
    @0
    @2
    @1
    cK
    atlpos
    adantr
    @0
    @4
    @1
    @3
    cK
    c.0
    @3
    eqid
    #
    atnle0.z
    atl0cl
    adantr
    @1
    @5
    @0
    cA
    @3
    cP
    cK
    @7
    atnle0.a
    atbase
    adantl
    cA
    @6
    cal
    cP
    cK
    c.0
    atnle0.z
    @6
    eqid
    #
    atnle0.a
    atcvr0
    @3
    @6
    cK
    c.le
    c.0
    cP
    @7
    atnle0.l
    @8
    cvrnle
    syl31anc
end
