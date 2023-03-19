include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "wbr.mm"
include "co.mm"
include "clat.mm"
include "wceq.mm"
include "simp11.mm"
include "hllat.mm"
include "syl.mm"
include "simp13.mm"
include "simp2l.mm"
include "simp2r.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "simp12.mm"
include "latmcl.mm"
include "latjcom.mm"
include "latjcl.mm"
include "latmcom.mm"
include "oveq2d.mm"
include "simp3.mm"
include "llnmod1i2.mm"
include "syl321anc.mm"
include "3eqtr4d.mm"
include "oveq1d.mm"
include "3eqtr4rd.mm"

theorem llnmod2i2
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


  assert |- ( ( ( K e. HL /\ X e. B /\ Y e. B ) /\ ( P e. A /\ Q e. A ) /\ Y .<_ X ) -> ( ( X ./\ ( P .\/ Q ) ) .\/ Y ) = ( X ./\ ( ( P .\/ Q ) .\/ Y ) ) )

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
    cY
    cX
    c.le
    wbr
    #
    w3a
    #
    cY
    cP
    cQ
    c.or
    co
    #
    cX
    c.an
    co
    #
    c.or
    co
    #
    @10
    cY
    c.or
    co
    #
    cX
    @9
    cY
    c.or
    co
    #
    c.an
    co
    #
    cX
    @9
    c.an
    co
    #
    cY
    c.or
    co
    @8
    cK
    clat
    wcel
    #
    @2
    @10
    cB
    wcel
    #
    @11
    @12
    wceq
    @8
    @0
    @16
    @0
    @1
    @2
    @6
    @7
    simp11
    #
    cK
    hllat
    syl
    #
    @0
    @1
    @2
    @6
    @7
    simp13
    #
    @8
    @16
    @9
    cB
    wcel
    #
    @1
    @17
    @19
    @8
    @0
    @4
    @5
    @21
    @18
    @3
    @4
    @5
    @7
    simp2l
    #
    @3
    @4
    @5
    @7
    simp2r
    #
    cA
    cB
    c.or
    cK
    cP
    cQ
    atmod.b
    atmod.j
    atmod.a
    hlatjcl
    syl3anc
    #
    @0
    @1
    @2
    @6
    @7
    simp12
    #
    cB
    cK
    c.an
    @9
    cX
    atmod.b
    atmod.m
    latmcl
    syl3anc
    cB
    c.or
    cK
    cY
    @10
    atmod.b
    atmod.j
    latjcom
    syl3anc
    @8
    cX
    cY
    @9
    c.or
    co
    #
    c.an
    co
    #
    @26
    cX
    c.an
    co
    #
    @14
    @11
    @8
    @16
    @1
    @26
    cB
    wcel
    #
    @27
    @28
    wceq
    @19
    @25
    @8
    @16
    @2
    @21
    @29
    @19
    @20
    @24
    cB
    c.or
    cK
    cY
    @9
    atmod.b
    atmod.j
    latjcl
    syl3anc
    cB
    cK
    c.an
    cX
    @26
    atmod.b
    atmod.m
    latmcom
    syl3anc
    @8
    @13
    @26
    cX
    c.an
    @8
    @16
    @21
    @2
    @13
    @26
    wceq
    @19
    @24
    @20
    cB
    c.or
    cK
    @9
    cY
    atmod.b
    atmod.j
    latjcom
    syl3anc
    oveq2d
    @8
    @0
    @2
    @1
    @4
    @5
    @7
    @11
    @28
    wceq
    @18
    @20
    @25
    @22
    @23
    @3
    @6
    @7
    simp3
    cA
    cB
    cP
    cQ
    c.or
    cK
    c.le
    c.an
    cY
    cX
    atmod.b
    atmod.l
    atmod.j
    atmod.m
    atmod.a
    llnmod1i2
    syl321anc
    3eqtr4d
    @8
    @15
    @10
    cY
    c.or
    @8
    @16
    @1
    @21
    @15
    @10
    wceq
    @19
    @25
    @24
    cB
    cK
    c.an
    cX
    @9
    atmod.b
    atmod.m
    latmcom
    syl3anc
    oveq1d
    3eqtr4rd
end
