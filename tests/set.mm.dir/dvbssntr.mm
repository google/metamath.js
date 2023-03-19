include "cdv.mm"
include "co.mm"
include "cdm.mm"
include "cnt.mm"
include "cfv.mm"
include "cc.mm"
include "cxp.mm"
include "wss.mm"
include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "cmin.mm"
include "cdiv.mm"
include "cmpt.mm"
include "climc.mm"
include "ciun.mm"
include "wceq.mm"
include "wf.mm"
include "wa.mm"
include "dvfval.mm"
include "syl3anc.mm"
include "simprd.mm"
include "dmss.mm"
include "syl.mm"
include "dmxpss.mm"
include "syl6ss.mm"

theorem dvbssntr
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cF: class F
  let cJ: class J
  let cK: class K
  let vx: setvar x
  let vz: setvar z
  let cB: class B
  let cC: class C
  assume dvcl.s: |- ( ph -> S C_ CC )
  assume dvcl.f: |- ( ph -> F : A --> CC )
  assume dvcl.a: |- ( ph -> A C_ S )
  assume dvbssntr.j: |- J = ( K |`t S )
  assume dvbssntr.k: |- K = ( TopOpen ` CCfld )


  assert |- ( ph -> dom ( S _D F ) C_ ( ( int ` J ) ` A ) )

  proof
    wph
    cS
    cF
    cdv
    co
    #
    cdm
    #
    cA
    cJ
    cnt
    cfv
    cfv
    #
    cc
    cxp
    #
    cdm
    #
    @2
    wph
    @0
    @3
    wss
    #
    @1
    @4
    wss
    wph
    @0
    vx
    @2
    vx
    cv
    #
    csn
    #
    vz
    cA
    @7
    cdif
    vz
    cv
    #
    cF
    cfv
    @6
    cF
    cfv
    cmin
    co
    @8
    @6
    cmin
    co
    cdiv
    co
    cmpt
    @6
    climc
    co
    cxp
    ciun
    wceq
    #
    @5
    wph
    cS
    cc
    wss
    cA
    cc
    cF
    wf
    cA
    cS
    wss
    @9
    @5
    wa
    dvcl.s
    dvcl.f
    dvcl.a
    vx
    vz
    cA
    cS
    cJ
    cF
    cK
    dvbssntr.j
    dvbssntr.k
    dvfval
    syl3anc
    simprd
    @0
    @3
    dmss
    syl
    @2
    cc
    dmxpss
    syl6ss
end
