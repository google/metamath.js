include "csumge0.mm"
include "cfv.mm"
include "cpnf.mm"
include "crn.mm"
include "wcel.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "cv.mm"
include "csu.mm"
include "cmpt.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cif.mm"
include "fge0icoicc.mm"
include "sge0vald.mm"
include "fge0npnf.mm"
include "iffalsed.mm"
include "eqtrd.mm"

theorem sge0reval
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cV: class V
  let cX: class X
  let vk: setvar k
  assume sge0reval.x: |- ( ph -> X e. V )
  assume sge0reval.f: |- ( ph -> F : X --> ( 0 [,) +oo ) )

  disjoint F x
  disjoint F y
  disjoint x y
  disjoint X x
  disjoint k x
  assert |- ( ph -> ( sum^ ` F ) = sup ( ran ( x e. ( ~P X i^i Fin ) |-> sum_ y e. x ( F ` y ) ) , RR* , < ) )

  proof
    wph
    cF
    csumge0
    cfv
    cpnf
    cF
    crn
    wcel
    #
    cpnf
    vx
    cX
    cpw
    cfn
    cin
    vx
    cv
    vy
    cv
    cF
    cfv
    vy
    csu
    cmpt
    crn
    cxr
    clt
    csup
    #
    cif
    @1
    wph
    vx
    vy
    cF
    cV
    cX
    sge0reval.x
    wph
    cF
    cX
    sge0reval.f
    fge0icoicc
    sge0vald
    wph
    @0
    cpnf
    @1
    wph
    cF
    cX
    sge0reval.f
    fge0npnf
    iffalsed
    eqtrd
end
