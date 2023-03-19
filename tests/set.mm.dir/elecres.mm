include "cres.mm"
include "cec.mm"
include "wcel.mm"
include "wbr.mm"
include "wa.mm"
include "wrel.mm"
include "wb.mm"
include "relres.mm"
include "relelec.mm"
include "ax-mp.mm"
include "brresALTV.mm"
include "syl5bb.mm"

theorem elecres
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cV: class V


  assert |- ( C e. V -> ( C e. [ B ] ( R |` A ) <-> ( B e. A /\ B R C ) ) )

  proof
    cC
    cB
    cR
    cA
    cres
    #
    cec
    wcel
    #
    cB
    cC
    @0
    wbr
    #
    cC
    cV
    wcel
    cB
    cA
    wcel
    cB
    cC
    cR
    wbr
    wa
    @0
    wrel
    @1
    @2
    wb
    cR
    cA
    relres
    cC
    cB
    @0
    relelec
    ax-mp
    cA
    cB
    cC
    cR
    cV
    brresALTV
    syl5bb
end
