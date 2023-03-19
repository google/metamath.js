include "wcel.mm"
include "c2.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "wne.mm"
include "wrex.mm"
include "hashge2el2dif.mm"
include "hashge2el2difr.mm"
include "impbida.mm"

theorem hashge2el2difb
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let cV: class V
  let vz: setvar z

  disjoint x y
  disjoint D x
  disjoint D y
  disjoint V x
  disjoint V y
  disjoint x z
  disjoint y z
  disjoint D z
  assert |- ( D e. V -> ( 2 <_ ( # ` D ) <-> E. x e. D E. y e. D x =/= y ) )

  proof
    cD
    cV
    wcel
    c2
    cD
    chash
    cfv
    cle
    wbr
    vx
    cv
    vy
    cv
    wne
    vy
    cD
    wrex
    vx
    cD
    wrex
    vx
    vy
    cD
    cV
    hashge2el2dif
    vx
    vy
    cD
    cV
    hashge2el2difr
    impbida
end
