include "chom.mm"
include "cfv.mm"
include "cv.mm"
include "crngh.mm"
include "co.mm"
include "cmpt2.mm"
include "wceq.mm"
include "cxp.mm"
include "wfn.mm"
include "eqid.mm"
include "rngchomfvalALTV.mm"
include "ovex.mm"
include "fnmpt2i.mm"
include "fneq1.mm"
include "mpbiri.mm"
include "fnhomeqhomf.mm"
include "3syl.mm"
include "eqtrd.mm"

theorem rngchomffvalALTV
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let cU: class U
  let cF: class F
  let cV: class V
  let vk: setvar k
  assume rngchomffvalALTV.c: |- C = ( RngCatALTV ` U )
  assume rngchomffvalALTV.b: |- B = ( Base ` C )
  assume rngchomffvalALTV.u: |- ( ph -> U e. V )
  assume rngchomffvalALTV.h: |- F = ( Homf ` C )

  disjoint B x
  disjoint B y
  disjoint x y
  disjoint U x
  disjoint U y
  disjoint ph x
  disjoint ph y
  disjoint k x
  assert |- ( ph -> F = ( x e. B , y e. B |-> ( x RngHomo y ) ) )

  proof
    wph
    cF
    cC
    chom
    cfv
    #
    vx
    vy
    cB
    cB
    vx
    cv
    #
    vy
    cv
    #
    crngh
    co
    #
    cmpt2
    #
    wph
    @0
    @4
    wceq
    #
    @0
    cB
    cB
    cxp
    #
    wfn
    #
    cF
    @0
    wceq
    wph
    vx
    vy
    cB
    cC
    cU
    @0
    cV
    rngchomffvalALTV.c
    rngchomffvalALTV.b
    rngchomffvalALTV.u
    @0
    eqid
    #
    rngchomfvalALTV
    #
    @5
    @7
    @4
    @6
    wfn
    vx
    vy
    cB
    cB
    @3
    @4
    @4
    eqid
    @1
    @2
    crngh
    ovex
    fnmpt2i
    @6
    @0
    @4
    fneq1
    mpbiri
    cB
    cC
    cF
    @0
    rngchomffvalALTV.h
    rngchomffvalALTV.b
    @8
    fnhomeqhomf
    3syl
    @9
    eqtrd
end
