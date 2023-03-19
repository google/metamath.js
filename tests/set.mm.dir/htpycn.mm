include "chtpy.mm"
include "co.mm"
include "cii.mm"
include "ctx.mm"
include "ccn.mm"
include "cv.mm"
include "wcel.mm"
include "cc0.mm"
include "cfv.mm"
include "wceq.mm"
include "c1.mm"
include "wa.mm"
include "wral.mm"
include "ishtpy.mm"
include "simpl.mm"
include "syl6bi.mm"
include "ssrdv.mm"

theorem htpycn
  let wph: wff ph
  let cF: class F
  let cG: class G
  let cJ: class J
  let cK: class K
  let cX: class X
  let cA: class A
  let vs: setvar s
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let cH: class H
  let cM: class M
  let vj: setvar j
  let vk: setvar k
  let vz: setvar z
  assume ishtpy.1: |- ( ph -> J e. ( TopOn ` X ) )
  assume ishtpy.3: |- ( ph -> F e. ( J Cn K ) )
  assume ishtpy.4: |- ( ph -> G e. ( J Cn K ) )


  assert |- ( ph -> ( F ( J Htpy K ) G ) C_ ( ( J tX II ) Cn K ) )

  proof
    wph
    vh
    cF
    cG
    cJ
    cK
    chtpy
    co
    co
    #
    cJ
    cii
    ctx
    co
    cK
    ccn
    co
    #
    wph
    vh
    cv
    #
    @0
    wcel
    @2
    @1
    wcel
    #
    vs
    cv
    #
    cc0
    @2
    co
    @4
    cF
    cfv
    wceq
    @4
    c1
    @2
    co
    @4
    cG
    cfv
    wceq
    wa
    vs
    cX
    wral
    #
    wa
    @3
    wph
    cF
    cG
    @2
    cJ
    cK
    cX
    vs
    ishtpy.1
    ishtpy.3
    ishtpy.4
    ishtpy
    @3
    @5
    simpl
    syl6bi
    ssrdv
end
