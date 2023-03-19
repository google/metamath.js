include "cal.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wceq.mm"
include "wa.mm"
include "cple.mm"
include "cfv.mm"
include "cplt.mm"
include "eqid.mm"
include "atl0le.mm"
include "3adant3.mm"
include "adantr.mm"
include "atbase.mm"
include "cvrlt.mm"
include "syl3anl3.mm"
include "cpo.mm"
include "wb.mm"
include "atlpos.mm"
include "3ad2ant1.mm"
include "atl0cl.mm"
include "3ad2ant3.mm"
include "simpl2.mm"
include "atcvr0.mm"
include "3adant2.mm"
include "cvrnbtwn3.mm"
include "syl131anc.mm"
include "mpbi2and.mm"
include "eqcomd.mm"
include "ex.mm"
include "breq1.mm"
include "syl5ibrcom.mm"
include "impbid.mm"

theorem atcvreq0
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let c.0: class .0.
  assume atcvreq0.b: |- B = ( Base ` K )
  assume atcvreq0.l: |- .<_ = ( le ` K )
  assume atcvreq0.z: |- .0. = ( 0. ` K )
  assume atcvreq0.c: |- C = ( <o ` K )
  assume atcvreq0.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. AtLat /\ X e. B /\ P e. A ) -> ( X C P <-> X = .0. ) )

  proof
    cK
    cal
    wcel
    #
    cX
    cB
    wcel
    #
    cP
    cA
    wcel
    #
    w3a
    #
    cX
    cP
    cC
    wbr
    #
    cX
    c.0
    wceq
    #
    @3
    @4
    @5
    @3
    @4
    wa
    #
    c.0
    cX
    @6
    c.0
    cX
    cK
    cple
    cfv
    #
    wbr
    #
    cX
    cP
    cK
    cplt
    cfv
    #
    wbr
    #
    c.0
    cX
    wceq
    #
    @3
    @8
    @4
    @0
    @1
    @8
    @2
    cB
    cK
    @7
    cX
    c.0
    atcvreq0.b
    @7
    eqid
    #
    atcvreq0.z
    atl0le
    3adant3
    adantr
    @2
    @0
    @1
    cP
    cB
    wcel
    #
    @4
    @10
    cA
    cB
    cP
    cK
    atcvreq0.b
    atcvreq0.a
    atbase
    #
    cal
    cB
    cC
    @9
    cK
    cX
    cP
    atcvreq0.b
    @9
    eqid
    #
    atcvreq0.c
    cvrlt
    syl3anl3
    @6
    cK
    cpo
    wcel
    #
    c.0
    cB
    wcel
    #
    @13
    @1
    c.0
    cP
    cC
    wbr
    #
    @8
    @10
    wa
    @11
    wb
    @3
    @16
    @4
    @0
    @1
    @16
    @2
    cK
    atlpos
    3ad2ant1
    adantr
    @3
    @17
    @4
    @0
    @1
    @17
    @2
    cB
    cK
    c.0
    atcvreq0.b
    atcvreq0.z
    atl0cl
    3ad2ant1
    adantr
    @3
    @13
    @4
    @2
    @0
    @13
    @1
    @14
    3ad2ant3
    adantr
    @0
    @1
    @2
    @4
    simpl2
    @3
    @18
    @4
    @0
    @2
    @18
    @1
    cA
    cC
    cal
    cP
    cK
    c.0
    atcvreq0.z
    atcvreq0.c
    atcvreq0.a
    atcvr0
    3adant2
    #
    adantr
    cB
    cC
    @9
    cK
    @7
    c.0
    cP
    cX
    atcvreq0.b
    @12
    @15
    atcvreq0.c
    cvrnbtwn3
    syl131anc
    mpbi2and
    eqcomd
    ex
    @3
    @4
    @5
    @18
    @19
    cX
    c.0
    cP
    cC
    breq1
    syl5ibrcom
    impbid
end
