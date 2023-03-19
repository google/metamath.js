include "ctop.mm"
include "wcel.mm"
include "ctg.mm"
include "cfv.mm"
include "wceq.mm"
include "tgtop.mm"
include "eqeqan12d.mm"
include "biimp3a.mm"

theorem tgtop11
  let cJ: class J
  let cK: class K


  assert |- ( ( J e. Top /\ K e. Top /\ ( topGen ` J ) = ( topGen ` K ) ) -> J = K )

  proof
    cJ
    ctop
    wcel
    #
    cK
    ctop
    wcel
    #
    cJ
    ctg
    cfv
    #
    cK
    ctg
    cfv
    #
    wceq
    cJ
    cK
    wceq
    @0
    @1
    @2
    cJ
    @3
    cK
    cJ
    tgtop
    cK
    tgtop
    eqeqan12d
    biimp3a
end
