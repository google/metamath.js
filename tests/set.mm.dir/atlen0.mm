include "cal.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wa.mm"
include "cplt.mm"
include "cfv.mm"
include "wne.mm"
include "simpl1.mm"
include "atl0cl.mm"
include "syl.mm"
include "simpl2.mm"
include "3jca.mm"
include "ccvr.mm"
include "simpl3.mm"
include "atbase.mm"
include "eqid.mm"
include "atcvr0.mm"
include "syl2anc.mm"
include "cvrlt.mm"
include "syl31anc.mm"
include "simpr.mm"
include "cpo.mm"
include "wi.mm"
include "atlpos.mm"
include "pltletr.mm"
include "syl13anc.mm"
include "mp2and.mm"
include "pltne.mm"
include "sylc.mm"
include "necomd.mm"

theorem atlen0
  let cA: class A
  let cB: class B
  let cP: class P
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let c.0: class .0.
  assume atlen0.b: |- B = ( Base ` K )
  assume atlen0.l: |- .<_ = ( le ` K )
  assume atlen0.z: |- .0. = ( 0. ` K )
  assume atlen0.a: |- A = ( Atoms ` K )


  assert |- ( ( ( K e. AtLat /\ X e. B /\ P e. A ) /\ P .<_ X ) -> X =/= .0. )

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
    cP
    cX
    c.le
    wbr
    #
    wa
    #
    c.0
    cX
    @5
    @0
    c.0
    cB
    wcel
    #
    @1
    w3a
    c.0
    cX
    cK
    cplt
    cfv
    #
    wbr
    #
    c.0
    cX
    wne
    @5
    @0
    @6
    @1
    @0
    @1
    @2
    @4
    simpl1
    #
    @5
    @0
    @6
    @9
    cB
    cK
    c.0
    atlen0.b
    atlen0.z
    atl0cl
    syl
    #
    @0
    @1
    @2
    @4
    simpl2
    #
    3jca
    @5
    c.0
    cP
    @7
    wbr
    #
    @4
    @8
    @5
    @0
    @6
    cP
    cB
    wcel
    #
    c.0
    cP
    cK
    ccvr
    cfv
    #
    wbr
    #
    @12
    @9
    @10
    @5
    @2
    @13
    @0
    @1
    @2
    @4
    simpl3
    #
    cA
    cB
    cP
    cK
    atlen0.b
    atlen0.a
    atbase
    syl
    #
    @5
    @0
    @2
    @15
    @9
    @16
    cA
    @14
    cal
    cP
    cK
    c.0
    atlen0.z
    @14
    eqid
    #
    atlen0.a
    atcvr0
    syl2anc
    cal
    cB
    @14
    @7
    cK
    c.0
    cP
    atlen0.b
    @7
    eqid
    #
    @18
    cvrlt
    syl31anc
    @3
    @4
    simpr
    @5
    cK
    cpo
    wcel
    #
    @6
    @13
    @1
    @12
    @4
    wa
    @8
    wi
    @5
    @0
    @20
    @9
    cK
    atlpos
    syl
    @10
    @17
    @11
    cB
    @7
    cK
    c.le
    c.0
    cP
    cX
    atlen0.b
    atlen0.l
    @19
    pltletr
    syl13anc
    mp2and
    cal
    cB
    cB
    @7
    cK
    c.0
    cX
    @19
    pltne
    sylc
    necomd
end
