include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "cuz.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "elnnuz.mm"
include "uzsubsubfz.mm"
include "sylanb.mm"

theorem uzsubsubfz1
  let cL: class L
  let cN: class N


  assert |- ( ( L e. NN /\ N e. ( ZZ>= ` L ) ) -> ( N - ( L - 1 ) ) e. ( 1 ... N ) )

  proof
    cL
    cn
    wcel
    cL
    c1
    cuz
    cfv
    wcel
    cN
    cL
    cuz
    cfv
    wcel
    cN
    cL
    c1
    cmin
    co
    cmin
    co
    c1
    cN
    cfz
    co
    wcel
    cL
    elnnuz
    cL
    c1
    cN
    uzsubsubfz
    sylanb
end
