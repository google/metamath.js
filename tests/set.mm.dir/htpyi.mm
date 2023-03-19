include "cv.mm"
include "cc0.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "c1.mm"
include "wa.mm"
include "wral.mm"
include "wcel.mm"
include "cii.mm"
include "ctx.mm"
include "ccn.mm"
include "chtpy.mm"
include "ishtpy.mm"
include "mpbid.mm"
include "simprd.mm"
include "oveq1.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "anbi12d.mm"
include "rspccva.mm"
include "sylan.mm"

theorem htpyi
  let wph: wff ph
  let cA: class A
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cK: class K
  let cX: class X
  let vs: setvar s
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let cM: class M
  let vj: setvar j
  let vk: setvar k
  let vz: setvar z
  assume ishtpy.1: |- ( ph -> J e. ( TopOn ` X ) )
  assume ishtpy.3: |- ( ph -> F e. ( J Cn K ) )
  assume ishtpy.4: |- ( ph -> G e. ( J Cn K ) )
  assume htpyi.1: |- ( ph -> H e. ( F ( J Htpy K ) G ) )


  assert |- ( ( ph /\ A e. X ) -> ( ( A H 0 ) = ( F ` A ) /\ ( A H 1 ) = ( G ` A ) ) )

  proof
    wph
    vs
    cv
    #
    cc0
    cH
    co
    #
    @0
    cF
    cfv
    #
    wceq
    #
    @0
    c1
    cH
    co
    #
    @0
    cG
    cfv
    #
    wceq
    #
    wa
    #
    vs
    cX
    wral
    #
    cA
    cX
    wcel
    cA
    cc0
    cH
    co
    #
    cA
    cF
    cfv
    #
    wceq
    #
    cA
    c1
    cH
    co
    #
    cA
    cG
    cfv
    #
    wceq
    #
    wa
    #
    wph
    cH
    cJ
    cii
    ctx
    co
    cK
    ccn
    co
    wcel
    #
    @8
    wph
    cH
    cF
    cG
    cJ
    cK
    chtpy
    co
    co
    wcel
    @16
    @8
    wa
    htpyi.1
    wph
    cF
    cG
    cH
    cJ
    cK
    cX
    vs
    ishtpy.1
    ishtpy.3
    ishtpy.4
    ishtpy
    mpbid
    simprd
    @7
    @15
    vs
    cA
    cX
    @0
    cA
    wceq
    #
    @3
    @11
    @6
    @14
    @17
    @1
    @9
    @2
    @10
    @0
    cA
    cc0
    cH
    oveq1
    @0
    cA
    cF
    fveq2
    eqeq12d
    @17
    @4
    @12
    @5
    @13
    @0
    cA
    c1
    cH
    oveq1
    @0
    cA
    cG
    fveq2
    eqeq12d
    anbi12d
    rspccva
    sylan
end
