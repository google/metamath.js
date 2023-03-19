include "chli.mm"
include "cv.mm"
include "cn.mm"
include "cmap.mm"
include "co.mm"
include "cima.mm"
include "wss.mm"
include "csh.mm"
include "cch.mm"
include "wceq.mm"
include "oveq1.mm"
include "imaeq2d.mm"
include "id.mm"
include "sseq12d.mm"
include "df-ch.mm"
include "elrab2.mm"

theorem isch
  let cH: class H
  let vh: setvar h


  assert |- ( H e. CH <-> ( H e. SH /\ ( ~~>v " ( H ^m NN ) ) C_ H ) )

  proof
    chli
    vh
    cv
    #
    cn
    cmap
    co
    #
    cima
    #
    @0
    wss
    chli
    cH
    cn
    cmap
    co
    #
    cima
    #
    cH
    wss
    vh
    cH
    csh
    cch
    @0
    cH
    wceq
    #
    @2
    @4
    @0
    cH
    @5
    @1
    @3
    chli
    @0
    cH
    cn
    cmap
    oveq1
    imaeq2d
    @5
    id
    sseq12d
    vh
    df-ch
    elrab2
end
