include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "cn0.mm"
include "cpnf.mm"
include "wceq.mm"
include "wo.mm"
include "cc0.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "w3o.mm"
include "hashnn0pnf.mm"
include "cn.mm"
include "elnn0.mm"
include "wne.mm"
include "exmidne.mm"
include "nngt1ne1.mm"
include "orbi2d.mm"
include "mpbiri.mm"
include "olcd.mm"
include "3orass.mm"
include "sylibr.mm"
include "3mix1.mm"
include "jaoi.mm"
include "sylbi.mm"
include "cr.mm"
include "1re.mm"
include "ltpnf.mm"
include "ax-mp.mm"
include "breq2.mm"
include "3mix3d.mm"
include "syl.mm"

theorem hashv01gt1
  let cM: class M
  let cV: class V


  assert |- ( M e. V -> ( ( # ` M ) = 0 \/ ( # ` M ) = 1 \/ 1 < ( # ` M ) ) )

  proof
    cM
    cV
    wcel
    cM
    chash
    cfv
    #
    cn0
    wcel
    #
    @0
    cpnf
    wceq
    #
    wo
    @0
    cc0
    wceq
    #
    @0
    c1
    wceq
    #
    c1
    @0
    clt
    wbr
    #
    w3o
    #
    cM
    cV
    hashnn0pnf
    @1
    @6
    @2
    @1
    @0
    cn
    wcel
    #
    @3
    wo
    @6
    @0
    elnn0
    @7
    @6
    @3
    @7
    @3
    @4
    @5
    wo
    #
    wo
    @6
    @7
    @8
    @3
    @7
    @8
    @4
    @0
    c1
    wne
    #
    wo
    @0
    c1
    exmidne
    @7
    @5
    @9
    @4
    @0
    nngt1ne1
    orbi2d
    mpbiri
    olcd
    @3
    @4
    @5
    3orass
    sylibr
    @3
    @4
    @5
    3mix1
    jaoi
    sylbi
    @2
    @5
    @3
    @4
    @2
    @5
    c1
    cpnf
    clt
    wbr
    #
    c1
    cr
    wcel
    @10
    1re
    c1
    ltpnf
    ax-mp
    @0
    cpnf
    c1
    clt
    breq2
    mpbiri
    3mix3d
    jaoi
    syl
end
