include "crli.mm"
include "wbr.mm"
include "crp.mm"
include "wcel.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "c1.mm"
include "csqrt.mm"
include "cdiv.mm"
include "cle.mm"
include "cr.mm"
include "wf.mm"
include "cdm.mm"
include "wa.mm"
include "wi.mm"
include "divsqrtsumlem.mm"
include "simp3i.mm"
include "sylan.mm"

theorem divsqrtsum2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vn: setvar n
  let cF: class F
  let cL: class L
  let vy: setvar y
  assume divsqrtsum.2: |- F = ( x e. RR+ |-> ( sum_ n e. ( 1 ... ( |_ ` x ) ) ( 1 / ( sqrt ` n ) ) - ( 2 x. ( sqrt ` x ) ) ) )
  assume divsqrsum2.1: |- ( ph -> F ~~>r L )

  disjoint n ph
  disjoint n x
  disjoint A n
  disjoint A x
  disjoint x y
  disjoint F y
  disjoint L y
  disjoint n y
  disjoint ph y
  assert |- ( ( ph /\ A e. RR+ ) -> ( abs ` ( ( F ` A ) - L ) ) <_ ( 1 / ( sqrt ` A ) ) )

  proof
    wph
    cF
    cL
    crli
    wbr
    #
    cA
    crp
    wcel
    #
    cA
    cF
    cfv
    cL
    cmin
    co
    cabs
    cfv
    c1
    cA
    csqrt
    cfv
    cdiv
    co
    cle
    wbr
    #
    divsqrsum2.1
    crp
    cr
    cF
    wf
    cF
    crli
    cdm
    wcel
    @0
    @1
    wa
    @2
    wi
    vx
    cA
    vn
    cF
    cL
    divsqrtsum.2
    divsqrtsumlem
    simp3i
    sylan
end
