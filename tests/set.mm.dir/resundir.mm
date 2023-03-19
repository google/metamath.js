include "cun.mm"
include "cvv.mm"
include "cxp.mm"
include "cin.mm"
include "cres.mm"
include "indir.mm"
include "df-res.mm"
include "uneq12i.mm"
include "3eqtr4i.mm"

theorem resundir
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A u. B ) |` C ) = ( ( A |` C ) u. ( B |` C ) )

  proof
    cA
    cB
    cun
    #
    cC
    cvv
    cxp
    #
    cin
    cA
    @1
    cin
    #
    cB
    @1
    cin
    #
    cun
    @0
    cC
    cres
    cA
    cC
    cres
    #
    cB
    cC
    cres
    #
    cun
    cA
    cB
    @1
    indir
    @0
    cC
    df-res
    @4
    @2
    @5
    @3
    cA
    cC
    df-res
    cB
    cC
    df-res
    uneq12i
    3eqtr4i
end
