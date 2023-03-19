include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "cgrp.mm"
include "wss.mm"
include "cress.mm"
include "co.mm"
include "wa.mm"
include "w3a.mm"
include "issubg.mm"
include "3anass.mm"
include "bitri.mm"
include "wb.mm"
include "symggrp.mm"
include "ibar.mm"
include "bicomd.mm"
include "syl.mm"
include "syl5bb.mm"

theorem pgrpsubgsymgbi
  let cA: class A
  let cB: class B
  let cP: class P
  let cG: class G
  let cV: class V
  assume pgrpsubgsymgbi.g: |- G = ( SymGrp ` A )
  assume pgrpsubgsymgbi.b: |- B = ( Base ` G )


  assert |- ( A e. V -> ( P e. ( SubGrp ` G ) <-> ( P C_ B /\ ( G |`s P ) e. Grp ) ) )

  proof
    cP
    cG
    csubg
    cfv
    wcel
    #
    cG
    cgrp
    wcel
    #
    cP
    cB
    wss
    #
    cG
    cP
    cress
    co
    cgrp
    wcel
    #
    wa
    #
    wa
    #
    cA
    cV
    wcel
    #
    @4
    @0
    @1
    @2
    @3
    w3a
    @5
    cB
    cP
    cG
    pgrpsubgsymgbi.b
    issubg
    @1
    @2
    @3
    3anass
    bitri
    @6
    @1
    @5
    @4
    wb
    cA
    cG
    cV
    pgrpsubgsymgbi.g
    symggrp
    @1
    @4
    @5
    @1
    @4
    ibar
    bicomd
    syl
    syl5bb
end
