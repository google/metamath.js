include "crn.mm"
include "cres.mm"
include "wfun.mm"
include "wa.mm"
include "ccom.mm"
include "funco.mm"
include "wss.mm"
include "wceq.mm"
include "ssid.mm"
include "cores.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "funeqi.mm"
include "sylibr.mm"

theorem funresfunco
  let cF: class F
  let cG: class G
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( Fun ( F |` ran G ) /\ Fun G ) -> Fun ( F o. G ) )

  proof
    cF
    cG
    crn
    #
    cres
    #
    wfun
    cG
    wfun
    wa
    @1
    cG
    ccom
    #
    wfun
    cF
    cG
    ccom
    #
    wfun
    @1
    cG
    funco
    @3
    @2
    @2
    @3
    @0
    @0
    wss
    @2
    @3
    wceq
    @0
    ssid
    cF
    cG
    @0
    cores
    ax-mp
    eqcomi
    funeqi
    sylibr
end
