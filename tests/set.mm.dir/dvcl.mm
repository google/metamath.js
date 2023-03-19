include "cdv.mm"
include "co.mm"
include "wbr.mm"
include "wa.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "cfv.mm"
include "cmin.mm"
include "cdiv.mm"
include "cmpt.mm"
include "climc.mm"
include "cc.mm"
include "limccl.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "crest.mm"
include "cnt.mm"
include "wcel.mm"
include "eqid.mm"
include "eldv.mm"
include "simplbda.mm"
include "sseldi.mm"

theorem dvcl
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let cF: class F
  let vx: setvar x
  let vz: setvar z
  let cK: class K
  let cJ: class J
  assume dvcl.s: |- ( ph -> S C_ CC )
  assume dvcl.f: |- ( ph -> F : A --> CC )
  assume dvcl.a: |- ( ph -> A C_ S )


  assert |- ( ( ph /\ B ( S _D F ) C ) -> C e. CC )

  proof
    wph
    cB
    cC
    cS
    cF
    cdv
    co
    wbr
    #
    wa
    vz
    cA
    cB
    csn
    cdif
    vz
    cv
    #
    cF
    cfv
    cB
    cF
    cfv
    cmin
    co
    @1
    cB
    cmin
    co
    cdiv
    co
    cmpt
    #
    cB
    climc
    co
    #
    cc
    cC
    cB
    @2
    limccl
    wph
    @0
    cB
    cA
    ccnfld
    ctopn
    cfv
    #
    cS
    crest
    co
    #
    cnt
    cfv
    cfv
    wcel
    cC
    @3
    wcel
    wph
    vz
    cA
    cB
    cC
    cS
    @5
    cF
    @2
    @4
    @5
    eqid
    @4
    eqid
    @2
    eqid
    dvcl.s
    dvcl.f
    dvcl.a
    eldv
    simplbda
    sseldi
end
