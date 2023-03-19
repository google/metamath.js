include "cdm.mm"
include "wcel.mm"
include "ccom.mm"
include "cfv.mm"
include "wceq.mm"
include "wfn.mm"
include "wfun.mm"
include "funfn.mm"
include "mpbi.mm"
include "fvco2.mm"
include "mpan.mm"
include "wn.mm"
include "c0.mm"
include "dmcoss.mm"
include "sseli.mm"
include "con3i.mm"
include "ndmfv.mm"
include "syl.mm"
include "fveq2d.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"

theorem fvco4i
  let cF: class F
  let cG: class G
  let cX: class X
  assume fvco4i.a: |- (/) = ( F ` (/) )
  assume fvco4i.b: |- Fun G


  assert |- ( ( F o. G ) ` X ) = ( F ` ( G ` X ) )

  proof
    cX
    cG
    cdm
    #
    wcel
    #
    cX
    cF
    cG
    ccom
    #
    cfv
    #
    cX
    cG
    cfv
    #
    cF
    cfv
    #
    wceq
    #
    cG
    @0
    wfn
    #
    @1
    @6
    cG
    wfun
    @7
    fvco4i.b
    cG
    funfn
    mpbi
    @0
    cF
    cG
    cX
    fvco2
    mpan
    @1
    wn
    #
    c0
    c0
    cF
    cfv
    @3
    @5
    fvco4i.a
    @8
    cX
    @2
    cdm
    #
    wcel
    #
    wn
    @3
    c0
    wceq
    @10
    @1
    @9
    @0
    cX
    cF
    cG
    dmcoss
    sseli
    con3i
    cX
    @2
    ndmfv
    syl
    @8
    @4
    c0
    cF
    cX
    cG
    ndmfv
    fveq2d
    3eqtr4a
    pm2.61i
end
