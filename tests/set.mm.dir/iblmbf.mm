include "cibl.mm"
include "cmbf.mm"
include "cr.mm"
include "cv.mm"
include "cfv.mm"
include "ci.mm"
include "cexp.mm"
include "co.mm"
include "cdiv.mm"
include "cre.mm"
include "cdm.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cif.mm"
include "csb.mm"
include "cmpt.mm"
include "citg2.mm"
include "c3.mm"
include "cfz.mm"
include "wral.mm"
include "crab.mm"
include "df-ibl.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "sseli.mm"

theorem iblmbf
  let cF: class F
  let vf: setvar f
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cG: class G
  let cK: class K
  let wph: wff ph
  let cT: class T
  let cV: class V


  assert |- ( F e. L^1 -> F e. MblFn )

  proof
    cibl
    cmbf
    cF
    cibl
    vx
    cr
    vy
    vx
    cv
    #
    vf
    cv
    #
    cfv
    ci
    vk
    cv
    cexp
    co
    cdiv
    co
    cre
    cfv
    @0
    @1
    cdm
    wcel
    cc0
    vy
    cv
    #
    cle
    wbr
    wa
    @2
    cc0
    cif
    csb
    cmpt
    citg2
    cfv
    cr
    wcel
    vk
    cc0
    c3
    cfz
    co
    wral
    #
    vf
    cmbf
    crab
    cmbf
    vx
    vy
    vf
    vk
    df-ibl
    @3
    vf
    cmbf
    ssrab2
    eqsstri
    sseli
end
