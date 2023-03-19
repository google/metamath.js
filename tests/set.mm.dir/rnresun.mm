include "cun.mm"
include "cres.mm"
include "crn.mm"
include "resundi.mm"
include "rneqi.mm"
include "rnun.mm"
include "eqtri.mm"

theorem rnresun
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ran ( F |` ( A u. B ) ) = ( ran ( F |` A ) u. ran ( F |` B ) )

  proof
    cF
    cA
    cB
    cun
    cres
    #
    crn
    cF
    cA
    cres
    #
    cF
    cB
    cres
    #
    cun
    #
    crn
    @1
    crn
    @2
    crn
    cun
    @0
    @3
    cF
    cA
    cB
    resundi
    rneqi
    @1
    @2
    rnun
    eqtri
end
