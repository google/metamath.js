include "con0.mm"
include "cin.mm"
include "eqid.mm"
include "grur1.mm"

theorem bj-grur1
  let cU: class U


  assert |- ( ( U e. Univ /\ U e. U. ( R1 " On ) ) -> U = ( R1 ` ( U i^i On ) ) )

  proof
    cU
    con0
    cin
    #
    cU
    @0
    eqid
    grur1
end
