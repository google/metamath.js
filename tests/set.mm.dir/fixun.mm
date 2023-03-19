include "cun.mm"
include "cid.mm"
include "cin.mm"
include "cdm.mm"
include "cfix.mm"
include "indir.mm"
include "dmeqi.mm"
include "dmun.mm"
include "eqtri.mm"
include "df-fix.mm"
include "uneq12i.mm"
include "3eqtr4i.mm"

theorem fixun
  let cA: class A
  let cB: class B


  assert |- Fix ( A u. B ) = ( Fix A u. Fix B )

  proof
    cA
    cB
    cun
    #
    cid
    cin
    #
    cdm
    #
    cA
    cid
    cin
    #
    cdm
    #
    cB
    cid
    cin
    #
    cdm
    #
    cun
    #
    @0
    cfix
    cA
    cfix
    #
    cB
    cfix
    #
    cun
    @2
    @3
    @5
    cun
    #
    cdm
    @7
    @1
    @10
    cA
    cB
    cid
    indir
    dmeqi
    @3
    @5
    dmun
    eqtri
    @0
    df-fix
    @8
    @4
    @9
    @6
    cA
    df-fix
    cB
    df-fix
    uneq12i
    3eqtr4i
end
