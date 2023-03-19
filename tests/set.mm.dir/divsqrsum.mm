include "crp.mm"
include "cr.mm"
include "wf.mm"
include "crli.mm"
include "cdm.mm"
include "wcel.mm"
include "c1.mm"
include "wbr.mm"
include "wa.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "csqrt.mm"
include "cdiv.mm"
include "cle.mm"
include "wi.mm"
include "divsqrtsumlem.mm"
include "simp2i.mm"

theorem divsqrsum
  let vx: setvar x
  let vn: setvar n
  let cF: class F
  let vy: setvar y
  let cL: class L
  let wph: wff ph
  let cA: class A
  assume divsqrtsum.2: |- F = ( x e. RR+ |-> ( sum_ n e. ( 1 ... ( |_ ` x ) ) ( 1 / ( sqrt ` n ) ) - ( 2 x. ( sqrt ` x ) ) ) )

  disjoint n x
  disjoint x y
  disjoint F y
  disjoint L y
  disjoint n y
  disjoint n ph
  disjoint ph y
  disjoint A n
  disjoint A x
  assert |- F e. dom ~~>r

  proof
    crp
    cr
    cF
    wf
    cF
    crli
    cdm
    wcel
    cF
    c1
    crli
    wbr
    c1
    crp
    wcel
    wa
    c1
    cF
    cfv
    c1
    cmin
    co
    cabs
    cfv
    c1
    c1
    csqrt
    cfv
    cdiv
    co
    cle
    wbr
    wi
    vx
    c1
    vn
    cF
    c1
    divsqrtsum.2
    divsqrtsumlem
    simp2i
end
