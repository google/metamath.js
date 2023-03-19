include "cv.mm"
include "cgsu.mm"
include "co.mm"
include "wceq.mm"
include "c1.mm"
include "cneg.mm"
include "chash.mm"
include "cfv.mm"
include "cexp.mm"
include "wa.mm"
include "cpmtr.mm"
include "crn.mm"
include "cword.mm"
include "wrex.mm"
include "cio.mm"
include "iotaex.mm"
include "eqid.mm"
include "psgnfval.mm"
include "fnmpti.mm"

theorem psgnfn
  let cB: class B
  let cD: class D
  let cF: class F
  let cG: class G
  let cN: class N
  let vp: setvar p
  let vs: setvar s
  let vw: setvar w
  let vx: setvar x
  assume psgnfn.g: |- G = ( SymGrp ` D )
  assume psgnfn.b: |- B = ( Base ` G )
  assume psgnfn.f: |- F = { p e. B | dom ( p \ _I ) e. Fin }
  assume psgnfn.n: |- N = ( pmSgn ` D )

  disjoint B p
  disjoint p s
  disjoint p w
  disjoint p x
  disjoint s w
  disjoint s x
  disjoint w x
  disjoint D s
  disjoint D w
  disjoint D x
  disjoint F x
  assert |- N Fn F

  proof
    vx
    cF
    vx
    cv
    cG
    vw
    cv
    #
    cgsu
    co
    wceq
    vs
    cv
    c1
    cneg
    @0
    chash
    cfv
    cexp
    co
    wceq
    wa
    vw
    cD
    cpmtr
    cfv
    crn
    #
    cword
    wrex
    #
    vs
    cio
    cN
    @2
    vs
    iotaex
    vx
    vw
    cB
    cD
    @1
    cF
    cG
    cN
    vs
    vp
    psgnfn.g
    psgnfn.b
    psgnfn.f
    @1
    eqid
    psgnfn.n
    psgnfval
    fnmpti
end
