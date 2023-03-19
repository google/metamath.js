include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "cple.mm"
include "cfv.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "clat.mm"
include "wb.mm"
include "hllat.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "atbase.mm"
include "3ad2ant3.mm"
include "eqid.mm"
include "latnle.mm"
include "syl3anc.mm"
include "cvr1.mm"
include "bitr3d.mm"

theorem cvr2N
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let c.lt: class .<
  let c.or: class .\/
  let cK: class K
  let cX: class X
  assume cvr2.b: |- B = ( Base ` K )
  assume cvr2.s: |- .< = ( lt ` K )
  assume cvr2.j: |- .\/ = ( join ` K )
  assume cvr2.c: |- C = ( <o ` K )
  assume cvr2.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. HL /\ X e. B /\ P e. A ) -> ( X .< ( X .\/ P ) <-> X C ( X .\/ P ) ) )

  proof
    cK
    chlt
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
    cK
    cple
    cfv
    #
    wbr
    wn
    #
    cX
    cX
    cP
    c.or
    co
    #
    c.lt
    wbr
    #
    cX
    @6
    cC
    wbr
    @3
    cK
    clat
    wcel
    #
    @1
    cP
    cB
    wcel
    #
    @5
    @7
    wb
    @0
    @1
    @8
    @2
    cK
    hllat
    3ad2ant1
    @0
    @1
    @2
    simp2
    @2
    @0
    @9
    @1
    cA
    cB
    cP
    cK
    cvr2.b
    cvr2.a
    atbase
    3ad2ant3
    cB
    c.lt
    c.or
    cK
    @4
    cX
    cP
    cvr2.b
    @4
    eqid
    #
    cvr2.s
    cvr2.j
    latnle
    syl3anc
    cA
    cB
    cC
    cP
    c.or
    cK
    @4
    cX
    cvr2.b
    @10
    cvr2.j
    cvr2.c
    cvr2.a
    cvr1
    bitr3d
end
