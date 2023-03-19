include "cms.mm"
include "cfv.mm"
include "wcel.mm"
include "cca.mm"
include "wa.mm"
include "cv.mm"
include "clm.mm"
include "cdm.mm"
include "c0.mm"
include "wne.mm"
include "wex.mm"
include "cxmt.mm"
include "cme.mm"
include "cmetmet.mm"
include "metxmet.mm"
include "syl.mm"
include "caun0.mm"
include "sylan.mm"
include "n0.mm"
include "sylib.mm"
include "cn.mm"
include "cif.mm"
include "cmpt.mm"
include "simpll.mm"
include "simpr.mm"
include "simplr.mm"
include "eqid.mm"
include "cmetcaulem.mm"
include "exlimddv.mm"

theorem cmetcau
  let cD: class D
  let cF: class F
  let cJ: class J
  let cX: class X
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cG: class G
  let cP: class P
  let wph: wff ph
  assume cmetcau.1: |- J = ( MetOpen ` D )


  assert |- ( ( D e. ( CMet ` X ) /\ F e. ( Cau ` D ) ) -> F e. dom ( ~~>t ` J ) )

  proof
    cD
    cX
    cms
    cfv
    wcel
    #
    cF
    cD
    cca
    cfv
    wcel
    #
    wa
    #
    vx
    cv
    #
    cX
    wcel
    #
    cF
    cJ
    clm
    cfv
    cdm
    wcel
    vx
    @2
    cX
    c0
    wne
    #
    @4
    vx
    wex
    @0
    cD
    cX
    cxmt
    cfv
    wcel
    #
    @1
    @5
    @0
    cD
    cX
    cme
    cfv
    wcel
    @6
    cD
    cX
    cmetmet
    cD
    cX
    metxmet
    syl
    cD
    cF
    cX
    caun0
    sylan
    vx
    cX
    n0
    sylib
    @2
    @4
    wa
    vy
    cD
    @3
    cF
    vy
    cn
    vy
    cv
    #
    cF
    cdm
    wcel
    @7
    cF
    cfv
    @3
    cif
    cmpt
    #
    cJ
    cX
    cmetcau.1
    @0
    @1
    @4
    simpll
    @2
    @4
    simpr
    @0
    @1
    @4
    simplr
    @8
    eqid
    cmetcaulem
    exlimddv
end
