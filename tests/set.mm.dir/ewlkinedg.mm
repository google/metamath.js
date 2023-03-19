include "cewlks.mm"
include "co.mm"
include "wcel.mm"
include "c1.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "cmin.mm"
include "cin.mm"
include "cle.mm"
include "wbr.mm"
include "cvv.mm"
include "cxnn0.mm"
include "wa.mm"
include "cdm.mm"
include "cword.mm"
include "cv.mm"
include "wral.mm"
include "w3a.mm"
include "wi.mm"
include "ewlkprop.mm"
include "wceq.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "ineq12d.mm"
include "breq2d.mm"
include "rspccv.mm"
include "3ad2ant3.mm"
include "syl.mm"
include "imp.mm"

theorem ewlkinedg
  let cS: class S
  let cF: class F
  let cG: class G
  let cI: class I
  let cK: class K
  let vf: setvar f
  let vg: setvar g
  let vi: setvar i
  let vk: setvar k
  let vs: setvar s
  let cW: class W
  assume ewlksfval.i: |- I = ( iEdg ` G )


  assert |- ( ( F e. ( G EdgWalks S ) /\ K e. ( 1 ..^ ( # ` F ) ) ) -> S <_ ( # ` ( ( I ` ( F ` ( K - 1 ) ) ) i^i ( I ` ( F ` K ) ) ) ) )

  proof
    cF
    cG
    cS
    cewlks
    co
    wcel
    #
    cK
    c1
    cF
    chash
    cfv
    cfzo
    co
    #
    wcel
    #
    cS
    cK
    c1
    cmin
    co
    #
    cF
    cfv
    #
    cI
    cfv
    #
    cK
    cF
    cfv
    #
    cI
    cfv
    #
    cin
    #
    chash
    cfv
    #
    cle
    wbr
    #
    @0
    cG
    cvv
    wcel
    cS
    cxnn0
    wcel
    wa
    #
    cF
    cI
    cdm
    cword
    wcel
    #
    cS
    vk
    cv
    #
    c1
    cmin
    co
    #
    cF
    cfv
    #
    cI
    cfv
    #
    @13
    cF
    cfv
    #
    cI
    cfv
    #
    cin
    #
    chash
    cfv
    #
    cle
    wbr
    #
    vk
    @1
    wral
    #
    w3a
    @2
    @10
    wi
    #
    cS
    vk
    cF
    cG
    cI
    ewlksfval.i
    ewlkprop
    @22
    @11
    @23
    @12
    @21
    @10
    vk
    cK
    @1
    @13
    cK
    wceq
    #
    @20
    @9
    cS
    cle
    @24
    @19
    @8
    chash
    @24
    @16
    @5
    @18
    @7
    @24
    @15
    @4
    cI
    @24
    @14
    @3
    cF
    @13
    cK
    c1
    cmin
    oveq1
    fveq2d
    fveq2d
    @24
    @17
    @6
    cI
    @13
    cK
    cF
    fveq2
    fveq2d
    ineq12d
    fveq2d
    breq2d
    rspccv
    3ad2ant3
    syl
    imp
end
