include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "wbr.mm"
include "co.mm"
include "wceq.mm"
include "cpmap.mm"
include "cfv.mm"
include "cpadd.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simprl.mm"
include "simprr.mm"
include "eqid.mm"
include "pmapjlln1.mm"
include "syl13anc.mm"
include "wi.mm"
include "clat.mm"
include "hllat.mm"
include "syl.mm"
include "atbase.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "simpl3.mm"
include "hlmod1i.mm"
include "mpan2d.mm"
include "3impia.mm"
include "eqcomd.mm"

theorem llnmod1i2
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cX: class X
  let cY: class Y
  assume atmod.b: |- B = ( Base ` K )
  assume atmod.l: |- .<_ = ( le ` K )
  assume atmod.j: |- .\/ = ( join ` K )
  assume atmod.m: |- ./\ = ( meet ` K )
  assume atmod.a: |- A = ( Atoms ` K )


  assert |- ( ( ( K e. HL /\ X e. B /\ Y e. B ) /\ ( P e. A /\ Q e. A ) /\ X .<_ Y ) -> ( X .\/ ( ( P .\/ Q ) ./\ Y ) ) = ( ( X .\/ ( P .\/ Q ) ) ./\ Y ) )

  proof
    cK
    chlt
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    w3a
    #
    cP
    cA
    wcel
    #
    cQ
    cA
    wcel
    #
    wa
    #
    cX
    cY
    c.le
    wbr
    #
    w3a
    cX
    cP
    cQ
    c.or
    co
    #
    c.or
    co
    #
    cY
    c.an
    co
    #
    cX
    @8
    cY
    c.an
    co
    c.or
    co
    #
    @3
    @6
    @7
    @10
    @11
    wceq
    #
    @3
    @6
    wa
    #
    @7
    @9
    cK
    cpmap
    cfv
    #
    cfv
    cX
    @14
    cfv
    @8
    @14
    cfv
    cK
    cpadd
    cfv
    #
    co
    wceq
    #
    @12
    @13
    @0
    @1
    @4
    @5
    @16
    @0
    @1
    @2
    @6
    simpl1
    #
    @0
    @1
    @2
    @6
    simpl2
    #
    @3
    @4
    @5
    simprl
    #
    @3
    @4
    @5
    simprr
    #
    cA
    cB
    @15
    cP
    cQ
    c.or
    cK
    @14
    cX
    atmod.b
    atmod.j
    atmod.a
    @14
    eqid
    #
    @15
    eqid
    #
    pmapjlln1
    syl13anc
    @13
    @0
    @1
    @8
    cB
    wcel
    #
    @2
    @7
    @16
    wa
    @12
    wi
    @17
    @18
    @13
    cK
    clat
    wcel
    #
    cP
    cB
    wcel
    #
    cQ
    cB
    wcel
    #
    @23
    @13
    @0
    @24
    @17
    cK
    hllat
    syl
    @13
    @4
    @25
    @19
    cA
    cB
    cP
    cK
    atmod.b
    atmod.a
    atbase
    syl
    @13
    @5
    @26
    @20
    cA
    cB
    cQ
    cK
    atmod.b
    atmod.a
    atbase
    syl
    cB
    c.or
    cK
    cP
    cQ
    atmod.b
    atmod.j
    latjcl
    syl3anc
    @0
    @1
    @2
    @6
    simpl3
    cB
    @15
    @14
    c.or
    cK
    c.le
    c.an
    cX
    @8
    cY
    atmod.b
    atmod.l
    atmod.j
    atmod.m
    @21
    @22
    hlmod1i
    syl13anc
    mpan2d
    3impia
    eqcomd
end
