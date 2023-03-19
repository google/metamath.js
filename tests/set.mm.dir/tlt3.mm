include "ctos.mm"
include "wcel.mm"
include "w3a.mm"
include "wceq.mm"
include "wbr.mm"
include "wo.mm"
include "w3o.mm"
include "cple.mm"
include "cfv.mm"
include "eqid.mm"
include "tlt2.mm"
include "cpo.mm"
include "wb.mm"
include "tospos.mm"
include "pleval2.mm"
include "orcom.mm"
include "syl6bb.mm"
include "syl3an1.mm"
include "orbi1d.mm"
include "mpbid.mm"
include "df-3or.mm"
include "sylibr.mm"

theorem tlt3
  let cB: class B
  let c.lt: class .<
  let cK: class K
  let cX: class X
  let cY: class Y
  assume tlt3.b: |- B = ( Base ` K )
  assume tlt3.l: |- .< = ( lt ` K )


  assert |- ( ( K e. Toset /\ X e. B /\ Y e. B ) -> ( X = Y \/ X .< Y \/ Y .< X ) )

  proof
    cK
    ctos
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
    cX
    cY
    wceq
    #
    cX
    cY
    c.lt
    wbr
    #
    wo
    #
    cY
    cX
    c.lt
    wbr
    #
    wo
    #
    @4
    @5
    @7
    w3o
    @3
    cX
    cY
    cK
    cple
    cfv
    #
    wbr
    #
    @7
    wo
    @8
    cB
    c.lt
    cK
    @9
    cX
    cY
    tlt3.b
    @9
    eqid
    #
    tlt3.l
    tlt2
    @3
    @10
    @6
    @7
    @0
    cK
    cpo
    wcel
    #
    @1
    @2
    @10
    @6
    wb
    cK
    tospos
    @12
    @1
    @2
    w3a
    @10
    @5
    @4
    wo
    @6
    cB
    c.lt
    cK
    @9
    cX
    cY
    tlt3.b
    @11
    tlt3.l
    pleval2
    @5
    @4
    orcom
    syl6bb
    syl3an1
    orbi1d
    mpbid
    @4
    @5
    @7
    df-3or
    sylibr
end
