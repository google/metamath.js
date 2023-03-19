include "cn.mm"
include "wcel.mm"
include "cc0.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "wa.mm"
include "caddc.mm"
include "cbc.mm"
include "cdiv.mm"
include "cmul.mm"
include "wceq.mm"
include "bcp1n.mm"
include "adantl.mm"
include "simpl.mm"
include "nncnd.mm"
include "1cnd.mm"
include "npcand.mm"
include "oveq1d.mm"
include "oveq12d.mm"
include "oveq2d.mm"
include "3eqtr3d.mm"

theorem bcm1nt
  let cK: class K
  let cN: class N


  assert |- ( ( N e. NN /\ K e. ( 0 ... ( N - 1 ) ) ) -> ( N _C K ) = ( ( ( N - 1 ) _C K ) x. ( N / ( N - K ) ) ) )

  proof
    cN
    cn
    wcel
    #
    cK
    cc0
    cN
    c1
    cmin
    co
    #
    cfz
    co
    wcel
    #
    wa
    #
    @1
    c1
    caddc
    co
    #
    cK
    cbc
    co
    #
    @1
    cK
    cbc
    co
    #
    @4
    @4
    cK
    cmin
    co
    #
    cdiv
    co
    #
    cmul
    co
    #
    cN
    cK
    cbc
    co
    @6
    cN
    cN
    cK
    cmin
    co
    #
    cdiv
    co
    #
    cmul
    co
    @2
    @5
    @9
    wceq
    @0
    cK
    @1
    bcp1n
    adantl
    @3
    @4
    cN
    cK
    cbc
    @3
    cN
    c1
    @3
    cN
    @0
    @2
    simpl
    nncnd
    @3
    1cnd
    npcand
    #
    oveq1d
    @3
    @8
    @11
    @6
    cmul
    @3
    @4
    cN
    @7
    @10
    cdiv
    @12
    @3
    @4
    cN
    cK
    cmin
    @12
    oveq1d
    oveq12d
    oveq2d
    3eqtr3d
end
