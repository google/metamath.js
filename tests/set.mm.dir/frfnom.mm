include "crdg.mm"
include "com.mm"
include "cres.mm"
include "wfn.mm"
include "wfun.mm"
include "cdm.mm"
include "wceq.mm"
include "rdgfun.mm"
include "funres.mm"
include "ax-mp.mm"
include "cin.mm"
include "dmres.mm"
include "wss.mm"
include "wlim.mm"
include "rdgdmlim.mm"
include "limomss.mm"
include "df-ss.mm"
include "mpbi.mm"
include "eqtri.mm"
include "df-fn.mm"
include "mpbir2an.mm"

theorem frfnom
  let cA: class A
  let cF: class F


  assert |- ( rec ( F , A ) |` _om ) Fn _om

  proof
    cF
    cA
    crdg
    #
    com
    cres
    #
    com
    wfn
    @1
    wfun
    #
    @1
    cdm
    #
    com
    wceq
    @0
    wfun
    @2
    cA
    cF
    rdgfun
    com
    @0
    funres
    ax-mp
    @3
    com
    @0
    cdm
    #
    cin
    #
    com
    @0
    com
    dmres
    com
    @4
    wss
    #
    @5
    com
    wceq
    @4
    wlim
    @6
    cA
    cF
    rdgdmlim
    @4
    limomss
    ax-mp
    com
    @4
    df-ss
    mpbi
    eqtri
    @1
    com
    df-fn
    mpbir2an
end
