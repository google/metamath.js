include "cnlm.mm"
include "cv.mm"
include "clmhm.mm"
include "co.mm"
include "cnghm.mm"
include "cin.mm"
include "cnmhm.mm"
include "df-nmhm.mm"
include "reldmmpt2.mm"

theorem reldmnmhm
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


  assert |- Rel dom NMHom

  proof
    vs
    vt
    cnlm
    cnlm
    vs
    cv
    #
    vt
    cv
    #
    clmhm
    co
    @0
    @1
    cnghm
    co
    cin
    cnmhm
    vt
    vs
    df-nmhm
    reldmmpt2
end
