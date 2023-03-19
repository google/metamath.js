include "cngp.mm"
include "cv.mm"
include "cnmo.mm"
include "co.mm"
include "ccnv.mm"
include "cr.mm"
include "cima.mm"
include "cnghm.mm"
include "df-nghm.mm"
include "reldmmpt2.mm"

theorem reldmnghm
  let vf: setvar f
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let cL: class L
  let cM: class M
  let cS: class S
  let cT: class T
  let cA: class A
  let cF: class F
  let wph: wff ph
  let cV: class V
  let cX: class X
  let cN: class N


  assert |- Rel dom NGHom

  proof
    vs
    vt
    cngp
    cngp
    vs
    cv
    vt
    cv
    cnmo
    co
    ccnv
    cr
    cima
    cnghm
    vt
    vs
    df-nghm
    reldmmpt2
end
