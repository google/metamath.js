include "cca.mm"
include "cfv.mm"
include "chil.mm"
include "cn.mm"
include "cmap.mm"
include "co.mm"
include "cin.mm"
include "wcel.mm"
include "cv.mm"
include "clm.mm"
include "wbr.mm"
include "wa.mm"
include "wrex.mm"
include "ccau.mm"
include "chli.mm"
include "anim1i.mm"
include "elin.mm"
include "r19.41v.mm"
include "3imtr4i.mm"
include "hhcau.mm"
include "eleq2i.mm"
include "cres.mm"
include "hhlm.mm"
include "breqi.mm"
include "vex.mm"
include "brres.mm"
include "bitri.mm"
include "rexbii.mm"

theorem hhcmpl
  let vx: setvar x
  let cD: class D
  let cU: class U
  let cF: class F
  let cJ: class J
  assume hhlm.1: |- U = <. <. +h , .h >. , normh >.
  assume hhlm.2: |- D = ( IndMet ` U )
  assume hhlm.3: |- J = ( MetOpen ` D )
  assume hhcmpl.c: |- ( F e. ( Cau ` D ) -> E. x e. ~H F ( ~~>t ` J ) x )

  disjoint F x
  assert |- ( F e. Cauchy -> E. x e. ~H F ~~>v x )

  proof
    cF
    cD
    cca
    cfv
    #
    chil
    cn
    cmap
    co
    #
    cin
    #
    wcel
    #
    cF
    vx
    cv
    #
    cJ
    clm
    cfv
    #
    wbr
    #
    cF
    @1
    wcel
    #
    wa
    #
    vx
    chil
    wrex
    #
    cF
    ccau
    wcel
    cF
    @4
    chli
    wbr
    #
    vx
    chil
    wrex
    cF
    @0
    wcel
    #
    @7
    wa
    @6
    vx
    chil
    wrex
    #
    @7
    wa
    @3
    @9
    @11
    @12
    @7
    hhcmpl.c
    anim1i
    cF
    @0
    @1
    elin
    @6
    @7
    vx
    chil
    r19.41v
    3imtr4i
    ccau
    @2
    cF
    cD
    cU
    hhlm.1
    hhlm.2
    hhcau
    eleq2i
    @10
    @8
    vx
    chil
    @10
    cF
    @4
    @5
    @1
    cres
    #
    wbr
    @8
    cF
    @4
    chli
    @13
    cD
    cU
    cJ
    hhlm.1
    hhlm.2
    hhlm.3
    hhlm
    breqi
    cF
    @4
    @5
    @1
    vx
    vex
    brres
    bitri
    rexbii
    3imtr4i
end
