include "wcel.mm"
include "cdom.mm"
include "wbr.mm"
include "wral.mm"
include "wa.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "ciun.mm"
include "eqid.mm"
include "cmap.mm"
include "co.mm"
include "ccrd.mm"
include "cdm.mm"
include "wacn.mm"
include "simpl.mm"
include "cvv.mm"
include "ovex.mm"
include "rgenw.mm"
include "iunexg.mm"
include "sylancl.mm"
include "numth3.mm"
include "syl.mm"
include "numacn.mm"
include "sylc.mm"
include "simpr.mm"
include "reldom.mm"
include "brrelexi.mm"
include "ralimi.mm"
include "sylan2.mm"
include "iundom2g.mm"
include "brrelex2i.mm"
include "3syl.mm"
include "iundomg.mm"

theorem iundom
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V

  disjoint A x
  disjoint B x
  assert |- ( ( A e. V /\ A. x e. A C ~<_ B ) -> U_ x e. A C ~<_ ( A X. B ) )

  proof
    cA
    cV
    wcel
    #
    cC
    cB
    cdom
    wbr
    #
    vx
    cA
    wral
    #
    wa
    #
    vx
    cA
    cC
    cB
    vx
    cA
    vx
    cv
    csn
    cC
    cxp
    ciun
    #
    @4
    eqid
    #
    @3
    @0
    vx
    cA
    cB
    cC
    cmap
    co
    #
    ciun
    #
    ccrd
    cdm
    #
    wcel
    #
    @7
    cA
    wacn
    wcel
    @0
    @2
    simpl
    #
    @3
    @7
    cvv
    wcel
    #
    @9
    @3
    @0
    @6
    cvv
    wcel
    #
    vx
    cA
    wral
    @11
    @10
    @12
    vx
    cA
    cB
    cC
    cmap
    ovex
    rgenw
    vx
    cA
    @6
    cV
    cvv
    iunexg
    sylancl
    @7
    cvv
    numth3
    syl
    cA
    cV
    @7
    numacn
    sylc
    #
    @0
    @2
    simpr
    #
    @3
    vx
    cA
    cC
    ciun
    #
    cvv
    wcel
    #
    cA
    cB
    cxp
    #
    @8
    wcel
    #
    @17
    @15
    wacn
    wcel
    @2
    @0
    cC
    cvv
    wcel
    #
    vx
    cA
    wral
    @16
    @1
    @19
    vx
    cA
    cC
    cB
    cdom
    reldom
    brrelexi
    ralimi
    vx
    cA
    cC
    cV
    cvv
    iunexg
    sylan2
    @3
    @4
    @17
    cdom
    wbr
    @17
    cvv
    wcel
    @18
    @3
    vx
    cA
    cC
    cB
    @4
    @5
    @13
    @14
    iundom2g
    @4
    @17
    cdom
    reldom
    brrelex2i
    @17
    cvv
    numth3
    3syl
    @15
    cvv
    @17
    numacn
    sylc
    iundomg
end
