include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "cn0.mm"
include "wnel.mm"
include "w3a.mm"
include "cle.mm"
include "wbr.mm"
include "cpnf.mm"
include "wceq.mm"
include "wi.mm"
include "wn.mm"
include "df-nel.mm"
include "pm2.21.mm"
include "sylbi.mm"
include "3ad2ant2.mm"
include "clt.mm"
include "cr.mm"
include "nn0re.mm"
include "ltpnf.mm"
include "syl.mm"
include "cxr.mm"
include "rexrd.mm"
include "pnfxr.mm"
include "xrltle.mm"
include "sylancl.mm"
include "mpd.mm"
include "breq2.mm"
include "syl5ibrcom.mm"
include "3ad2ant3.mm"
include "wo.mm"
include "hashnn0pnf.mm"
include "3ad2ant1.mm"
include "mpjaod.mm"

theorem hashnnn0genn0
  let cM: class M
  let cN: class N
  let cV: class V


  assert |- ( ( M e. V /\ ( # ` M ) e/ NN0 /\ N e. NN0 ) -> N <_ ( # ` M ) )

  proof
    cM
    cV
    wcel
    #
    cM
    chash
    cfv
    #
    cn0
    wnel
    #
    cN
    cn0
    wcel
    #
    w3a
    @1
    cn0
    wcel
    #
    cN
    @1
    cle
    wbr
    #
    @1
    cpnf
    wceq
    #
    @2
    @0
    @4
    @5
    wi
    #
    @3
    @2
    @4
    wn
    @7
    @1
    cn0
    df-nel
    @4
    @5
    pm2.21
    sylbi
    3ad2ant2
    @3
    @0
    @6
    @5
    wi
    @2
    @3
    @5
    @6
    cN
    cpnf
    cle
    wbr
    #
    @3
    cN
    cpnf
    clt
    wbr
    #
    @8
    @3
    cN
    cr
    wcel
    @9
    cN
    nn0re
    #
    cN
    ltpnf
    syl
    @3
    cN
    cxr
    wcel
    cpnf
    cxr
    wcel
    @9
    @8
    wi
    @3
    cN
    @10
    rexrd
    pnfxr
    cN
    cpnf
    xrltle
    sylancl
    mpd
    @1
    cpnf
    cN
    cle
    breq2
    syl5ibrcom
    3ad2ant3
    @0
    @2
    @4
    @6
    wo
    @3
    cM
    cV
    hashnn0pnf
    3ad2ant1
    mpjaod
end
