include "cxp.mm"
include "cqs.mm"
include "wcel.mm"
include "cv.mm"
include "cec.mm"
include "wceq.mm"
include "wrex.mm"
include "elqsi.mm"
include "cop.mm"
include "wi.mm"
include "eqid.mm"
include "eceq1.mm"
include "eqeq2d.mm"
include "imbi1d.mm"
include "wa.mm"
include "wb.mm"
include "eqcoms.mm"
include "syl5ibcom.mm"
include "optocl.mm"
include "rexlimiv.mm"
include "syl.mm"
include "eleq2s.mm"

theorem ecoptocl
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let vz: setvar z
  assume ecoptocl.1: |- S = ( ( B X. C ) /. R )
  assume ecoptocl.2: |- ( [ <. x , y >. ] R = A -> ( ph <-> ps ) )
  assume ecoptocl.3: |- ( ( x e. B /\ y e. C ) -> ph )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint R x
  disjoint R y
  disjoint ps x
  disjoint ps y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint C z
  disjoint R z
  disjoint ps z
  assert |- ( A e. S -> ps )

  proof
    wps
    cA
    cB
    cC
    cxp
    #
    cR
    cqs
    #
    cS
    cA
    @1
    wcel
    cA
    vz
    cv
    #
    cR
    cec
    #
    wceq
    #
    vz
    @0
    wrex
    wps
    vz
    @0
    cA
    cR
    elqsi
    @4
    wps
    vz
    @0
    cA
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    cR
    cec
    #
    wceq
    #
    wps
    wi
    @4
    wps
    wi
    vx
    vy
    @2
    cB
    cC
    @0
    @0
    eqid
    @7
    @2
    wceq
    #
    @9
    @4
    wps
    @10
    @8
    @3
    cA
    @7
    @2
    cR
    eceq1
    eqeq2d
    imbi1d
    @5
    cB
    wcel
    @6
    cC
    wcel
    wa
    wph
    @9
    wps
    ecoptocl.3
    wph
    wps
    wb
    @8
    cA
    ecoptocl.2
    eqcoms
    syl5ibcom
    optocl
    rexlimiv
    syl
    ecoptocl.1
    eleq2s
end
