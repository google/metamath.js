include "wcel.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "csumge0.mm"
include "cfv.mm"
include "crn.mm"
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
include "wceq.mm"
include "sge0val.mm"
include "syl2anc.mm"

theorem sge0vald
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cV: class V
  let cX: class X
  let vk: setvar k
  assume sge0vald.x: |- ( ph -> X e. V )
  assume sge0vald.f: |- ( ph -> F : X --> ( 0 [,] +oo ) )

  disjoint F x
  disjoint F y
  disjoint x y
  disjoint X x
  disjoint k x
  assert |- ( ph -> ( sum^ ` F ) = if ( +oo e. ran F , +oo , sup ( ran ( x e. ( ~P X i^i Fin ) |-> sum_ y e. x ( F ` y ) ) , RR* , < ) ) )

  proof
    wph
    cX
    cV
    wcel
    cX
    cc0
    cpnf
    cicc
    co
    cF
    wf
    cF
    csumge0
    cfv
    cpnf
    cF
    crn
    wcel
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
    cif
    wceq
    sge0vald.x
    sge0vald.f
    vx
    vy
    cF
    cV
    cX
    sge0val
    syl2anc
end
