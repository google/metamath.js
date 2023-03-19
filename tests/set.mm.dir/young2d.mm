include "ccxp.mm"
include "co.mm"
include "c1.mm"
include "cdiv.mm"
include "cmul.mm"
include "caddc.mm"
include "cle.mm"
include "rpred.mm"
include "rpcxpcld.mm"
include "rpreccld.mm"
include "amgmw2d.mm"
include "rpcnd.mm"
include "rpne0d.mm"
include "recidd.mm"
include "oveq2d.mm"
include "reccld.mm"
include "cxpmuld.mm"
include "cxp1d.mm"
include "3eqtr3d.mm"
include "oveq12d.mm"
include "divrecd.mm"
include "eqcomd.mm"
include "3brtr3d.mm"

theorem young2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let vk: setvar k
  let vx: setvar x
  assume young2d.0: |- ( ph -> A e. RR+ )
  assume young2d.1: |- ( ph -> P e. RR+ )
  assume young2d.2: |- ( ph -> B e. RR+ )
  assume young2d.3: |- ( ph -> Q e. RR+ )
  assume young2d.4: |- ( ph -> ( ( 1 / P ) + ( 1 / Q ) ) = 1 )


  assert |- ( ph -> ( A x. B ) <_ ( ( ( A ^c P ) / P ) + ( ( B ^c Q ) / Q ) ) )

  proof
    wph
    cA
    cP
    ccxp
    co
    #
    c1
    cP
    cdiv
    co
    #
    ccxp
    co
    #
    cB
    cQ
    ccxp
    co
    #
    c1
    cQ
    cdiv
    co
    #
    ccxp
    co
    #
    cmul
    co
    @0
    @1
    cmul
    co
    #
    @3
    @4
    cmul
    co
    #
    caddc
    co
    #
    cA
    cB
    cmul
    co
    @0
    cP
    cdiv
    co
    #
    @3
    cQ
    cdiv
    co
    #
    caddc
    co
    #
    cle
    wph
    @0
    @3
    @1
    @4
    wph
    cA
    cP
    young2d.0
    wph
    cP
    young2d.1
    rpred
    #
    rpcxpcld
    #
    wph
    cP
    young2d.1
    rpreccld
    wph
    cB
    cQ
    young2d.2
    wph
    cQ
    young2d.3
    rpred
    #
    rpcxpcld
    #
    wph
    cQ
    young2d.3
    rpreccld
    young2d.4
    amgmw2d
    wph
    @2
    cA
    @5
    cB
    cmul
    wph
    cA
    cP
    @1
    cmul
    co
    #
    ccxp
    co
    cA
    c1
    ccxp
    co
    @2
    cA
    wph
    @16
    c1
    cA
    ccxp
    wph
    cP
    wph
    cP
    young2d.1
    rpcnd
    #
    wph
    cP
    young2d.1
    rpne0d
    #
    recidd
    oveq2d
    wph
    cA
    cP
    @1
    young2d.0
    @12
    wph
    cP
    @17
    @18
    reccld
    cxpmuld
    wph
    cA
    wph
    cA
    young2d.0
    rpcnd
    cxp1d
    3eqtr3d
    wph
    cB
    cQ
    @4
    cmul
    co
    #
    ccxp
    co
    cB
    c1
    ccxp
    co
    @5
    cB
    wph
    @19
    c1
    cB
    ccxp
    wph
    cQ
    wph
    cQ
    young2d.3
    rpcnd
    #
    wph
    cQ
    young2d.3
    rpne0d
    #
    recidd
    oveq2d
    wph
    cB
    cQ
    @4
    young2d.2
    @14
    wph
    cQ
    @20
    @21
    reccld
    cxpmuld
    wph
    cB
    wph
    cB
    young2d.2
    rpcnd
    cxp1d
    3eqtr3d
    oveq12d
    wph
    @11
    @8
    wph
    @9
    @6
    @10
    @7
    caddc
    wph
    @0
    cP
    wph
    @0
    @13
    rpcnd
    @17
    @18
    divrecd
    wph
    @3
    cQ
    wph
    @3
    @15
    rpcnd
    @20
    @21
    divrecd
    oveq12d
    eqcomd
    3brtr3d
end
