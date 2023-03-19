include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "ccnv.mm"
include "cun.mm"
include "wn.mm"
include "wo.mm"
include "cxp.mm"
include "wb.mm"
include "cop.mm"
include "opelxpi.mm"
include "df-br.mm"
include "sylibr.mm"
include "cdif.mm"
include "breqi.mm"
include "brdif.mm"
include "bitri.mm"
include "baib.mm"
include "syl.mm"
include "brun.mm"
include "brcnvg.mm"
include "orbi2d.mm"
include "syl5bb.mm"
include "notbid.mm"
include "bitrd.mm"

theorem brdifun
  let cA: class A
  let cB: class B
  let cR: class R
  let c.lt: class .<
  let cX: class X
  assume swoer.1: |- R = ( ( X X. X ) \ ( .< u. `' .< ) )


  assert |- ( ( A e. X /\ B e. X ) -> ( A R B <-> -. ( A .< B \/ B .< A ) ) )

  proof
    cA
    cX
    wcel
    cB
    cX
    wcel
    wa
    #
    cA
    cB
    cR
    wbr
    #
    cA
    cB
    c.lt
    c.lt
    ccnv
    #
    cun
    #
    wbr
    #
    wn
    #
    cA
    cB
    c.lt
    wbr
    #
    cB
    cA
    c.lt
    wbr
    #
    wo
    #
    wn
    @0
    cA
    cB
    cX
    cX
    cxp
    #
    wbr
    #
    @1
    @5
    wb
    @0
    cA
    cB
    cop
    @9
    wcel
    @10
    cA
    cB
    cX
    cX
    opelxpi
    cA
    cB
    @9
    df-br
    sylibr
    @1
    @10
    @5
    @1
    cA
    cB
    @9
    @3
    cdif
    #
    wbr
    @10
    @5
    wa
    cA
    cB
    cR
    @11
    swoer.1
    breqi
    cA
    cB
    @9
    @3
    brdif
    bitri
    baib
    syl
    @0
    @4
    @8
    @4
    @6
    cA
    cB
    @2
    wbr
    #
    wo
    @0
    @8
    cA
    cB
    c.lt
    @2
    brun
    @0
    @12
    @7
    @6
    cA
    cB
    cX
    cX
    c.lt
    brcnvg
    orbi2d
    syl5bb
    notbid
    bitrd
end
