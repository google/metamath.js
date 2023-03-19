include "ccj.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "cmul.mm"
include "caddc.mm"
include "cneg.mm"
include "cr.mm"
include "wcel.mm"
include "wceq.mm"
include "cjcli.mm"
include "hicli.mm"
include "mulcli.mm"
include "cjaddi.mm"
include "cjcji.mm"
include "eqcomi.mm"
include "his1i.mm"
include "oveq12i.mm"
include "cjmuli.mm"
include "eqtr4i.mm"
include "oveq2i.mm"
include "addcomi.mm"
include "addcli.mm"
include "cjrebi.mm"
include "mpbir.mm"
include "renegcli.mm"
include "eqeltri.mm"

theorem normlem2
  let cB: class B
  let cS: class S
  let cF: class F
  let cG: class G
  assume normlem1.1: |- S e. CC
  assume normlem1.2: |- F e. ~H
  assume normlem1.3: |- G e. ~H
  assume normlem2.4: |- B = -u ( ( ( * ` S ) x. ( F .ih G ) ) + ( S x. ( G .ih F ) ) )


  assert |- B e. RR

  proof
    cB
    cS
    ccj
    cfv
    #
    cF
    cG
    csp
    co
    #
    cmul
    co
    #
    cS
    cG
    cF
    csp
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    cneg
    cr
    normlem2.4
    @5
    @5
    cr
    wcel
    @5
    ccj
    cfv
    #
    @5
    wceq
    @6
    @4
    @2
    caddc
    co
    #
    @5
    @6
    @2
    ccj
    cfv
    #
    @4
    ccj
    cfv
    #
    caddc
    co
    @7
    @2
    @4
    @0
    @1
    cS
    normlem1.1
    cjcli
    #
    cF
    cG
    normlem1.2
    normlem1.3
    hicli
    #
    mulcli
    #
    cS
    @3
    normlem1.1
    cG
    cF
    normlem1.3
    normlem1.2
    hicli
    #
    mulcli
    #
    cjaddi
    @4
    @8
    @2
    @9
    caddc
    @4
    @0
    ccj
    cfv
    #
    @1
    ccj
    cfv
    #
    cmul
    co
    @8
    cS
    @15
    @3
    @16
    cmul
    @15
    cS
    cS
    normlem1.1
    cjcji
    eqcomi
    cG
    cF
    normlem1.3
    normlem1.2
    his1i
    oveq12i
    @0
    @1
    @10
    @11
    cjmuli
    eqtr4i
    @2
    @0
    @3
    ccj
    cfv
    #
    cmul
    co
    @9
    @1
    @17
    @0
    cmul
    cF
    cG
    normlem1.2
    normlem1.3
    his1i
    oveq2i
    cS
    @3
    normlem1.1
    @13
    cjmuli
    eqtr4i
    oveq12i
    eqtr4i
    @2
    @4
    @12
    @14
    addcomi
    eqtr4i
    @5
    @2
    @4
    @12
    @14
    addcli
    cjrebi
    mpbir
    renegcli
    eqeltri
end
