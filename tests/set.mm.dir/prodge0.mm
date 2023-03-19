include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cmul.mm"
include "co.mm"
include "cle.mm"
include "wn.mm"
include "cneg.mm"
include "simpll.mm"
include "simplr.mm"
include "renegcld.mm"
include "simprl.mm"
include "simprr.mm"
include "mulgt0d.mm"
include "recnd.mm"
include "mulneg2d.mm"
include "breqtrd.mm"
include "expr.mm"
include "lt0neg1d.mm"
include "remulcld.mm"
include "3imtr4d.mm"
include "con3d.mm"
include "0red.mm"
include "lenltd.mm"
include "impr.mm"

theorem prodge0
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. RR /\ B e. RR ) /\ ( 0 < A /\ 0 <_ ( A x. B ) ) ) -> 0 <_ B )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    cc0
    cA
    clt
    wbr
    #
    cc0
    cA
    cB
    cmul
    co
    #
    cle
    wbr
    #
    cc0
    cB
    cle
    wbr
    #
    @2
    @3
    wa
    #
    @4
    cc0
    clt
    wbr
    #
    wn
    cB
    cc0
    clt
    wbr
    #
    wn
    @5
    @6
    @7
    @9
    @8
    @7
    cc0
    cB
    cneg
    #
    clt
    wbr
    #
    cc0
    @4
    cneg
    #
    clt
    wbr
    #
    @9
    @8
    @2
    @3
    @11
    @13
    @2
    @3
    @11
    wa
    #
    wa
    #
    cc0
    cA
    @10
    cmul
    co
    @12
    clt
    @15
    cA
    @10
    @0
    @1
    @14
    simpll
    #
    @15
    cB
    @0
    @1
    @14
    simplr
    #
    renegcld
    @2
    @3
    @11
    simprl
    @2
    @3
    @11
    simprr
    mulgt0d
    @15
    cA
    cB
    @15
    cA
    @16
    recnd
    @15
    cB
    @17
    recnd
    mulneg2d
    breqtrd
    expr
    @7
    cB
    @0
    @1
    @3
    simplr
    #
    lt0neg1d
    @7
    @4
    @7
    cA
    cB
    @0
    @1
    @3
    simpll
    @18
    remulcld
    #
    lt0neg1d
    3imtr4d
    con3d
    @7
    cc0
    @4
    @7
    0red
    #
    @19
    lenltd
    @7
    cc0
    cB
    @20
    @18
    lenltd
    3imtr4d
    impr
end
