include "wcel.mm"
include "cn0.mm"
include "coe1f.mm"
include "ffvelrnda.mm"

theorem coe1fvalcl
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cF: class F
  let cK: class K
  let cN: class N
  let vf: setvar f
  let vn: setvar n
  assume coe1fval.a: |- A = ( coe1 ` F )
  assume coe1f.b: |- B = ( Base ` P )
  assume coe1f.p: |- P = ( Poly1 ` R )
  assume coe1f.k: |- K = ( Base ` R )


  assert |- ( ( F e. B /\ N e. NN0 ) -> ( A ` N ) e. K )

  proof
    cF
    cB
    wcel
    cn0
    cK
    cN
    cA
    cA
    cB
    cP
    cR
    cF
    cK
    coe1fval.a
    coe1f.b
    coe1f.p
    coe1f.k
    coe1f
    ffvelrnda
end
