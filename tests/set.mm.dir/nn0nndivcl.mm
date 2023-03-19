include "cn0.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "cr.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "cdiv.mm"
include "co.mm"
include "elnnne0.mm"
include "nn0re.mm"
include "adantr.mm"
include "ad2antrl.mm"
include "simprr.mm"
include "3jca.mm"
include "sylan2b.mm"
include "redivcl.mm"
include "syl.mm"

theorem nn0nndivcl
  let cK: class K
  let cL: class L


  assert |- ( ( K e. NN0 /\ L e. NN ) -> ( K / L ) e. RR )

  proof
    cK
    cn0
    wcel
    #
    cL
    cn
    wcel
    #
    wa
    cK
    cr
    wcel
    #
    cL
    cr
    wcel
    #
    cL
    cc0
    wne
    #
    w3a
    #
    cK
    cL
    cdiv
    co
    cr
    wcel
    @1
    @0
    cL
    cn0
    wcel
    #
    @4
    wa
    #
    @5
    cL
    elnnne0
    @0
    @7
    wa
    @2
    @3
    @4
    @0
    @2
    @7
    cK
    nn0re
    adantr
    @6
    @3
    @0
    @4
    cL
    nn0re
    ad2antrl
    @0
    @6
    @4
    simprr
    3jca
    sylan2b
    cK
    cL
    redivcl
    syl
end
