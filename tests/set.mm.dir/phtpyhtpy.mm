include "cphtpy.mm"
include "cfv.mm"
include "co.mm"
include "cii.mm"
include "chtpy.mm"
include "cv.mm"
include "wcel.mm"
include "cc0.mm"
include "wceq.mm"
include "c1.mm"
include "wa.mm"
include "cicc.mm"
include "wral.mm"
include "isphtpy.mm"
include "simpl.mm"
include "syl6bi.mm"
include "ssrdv.mm"

theorem phtpyhtpy
  let wph: wff ph
  let cF: class F
  let cG: class G
  let cJ: class J
  let cA: class A
  let vs: setvar s
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let cH: class H
  let cK: class K
  let vj: setvar j
  assume isphtpy.2: |- ( ph -> F e. ( II Cn J ) )
  assume isphtpy.3: |- ( ph -> G e. ( II Cn J ) )


  assert |- ( ph -> ( F ( PHtpy ` J ) G ) C_ ( F ( II Htpy J ) G ) )

  proof
    wph
    vh
    cF
    cG
    cJ
    cphtpy
    cfv
    co
    #
    cF
    cG
    cii
    cJ
    chtpy
    co
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
    cc0
    vs
    cv
    #
    @2
    co
    cc0
    cF
    cfv
    wceq
    c1
    @4
    @2
    co
    c1
    cF
    cfv
    wceq
    wa
    vs
    cc0
    c1
    cicc
    co
    wral
    #
    wa
    @3
    wph
    cF
    cG
    @2
    cJ
    vs
    isphtpy.2
    isphtpy.3
    isphtpy
    @3
    @5
    simpl
    syl6bi
    ssrdv
end
