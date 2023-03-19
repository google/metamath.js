include "cumgr.mm"
include "wcel.mm"
include "cpr.mm"
include "cedg.mm"
include "cfv.mm"
include "wn.mm"
include "wnel.mm"
include "cvtx.mm"
include "wa.mm"
include "eqid.mm"
include "umgrpredgv.mm"
include "simpld.mm"
include "wceq.mm"
include "wne.mm"
include "umgredgne.mm"
include "eqneqall.mm"
include "mpsyl.mm"
include "pm2.65da.mm"
include "df-nel.mm"
include "sylibr.mm"

theorem umgrnloop2
  let cG: class G
  let cN: class N


  assert |- ( G e. UMGraph -> { N , N } e/ ( Edg ` G ) )

  proof
    cG
    cumgr
    wcel
    #
    cN
    cN
    cpr
    #
    cG
    cedg
    cfv
    #
    wcel
    #
    wn
    @1
    @2
    wnel
    @0
    @3
    cN
    cG
    cvtx
    cfv
    #
    wcel
    #
    @0
    @3
    wa
    #
    @5
    @5
    @2
    cG
    cN
    cN
    @4
    @4
    eqid
    @2
    eqid
    #
    umgrpredgv
    simpld
    cN
    cN
    wceq
    @6
    cN
    cN
    wne
    @5
    wn
    #
    cN
    eqid
    @2
    cG
    cN
    cN
    @7
    umgredgne
    @8
    cN
    cN
    eqneqall
    mpsyl
    pm2.65da
    @1
    @2
    df-nel
    sylibr
end
