include "cvv.mm"
include "wcel.mm"
include "c2.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "wne.mm"
include "wrex.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "hashge2el2dif.mm"
include "sylancr.mm"

theorem tglowdim1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cP: class P
  let cG: class G
  let cI: class I
  let c.mi: class .-
  assume tglowdim1.p: |- P = ( Base ` G )
  assume tglowdim1.d: |- .- = ( dist ` G )
  assume tglowdim1.i: |- I = ( Itv ` G )
  assume tglowdim1.g: |- ( ph -> G e. TarskiG )
  assume tglowdim1.1: |- ( ph -> 2 <_ ( # ` P ) )

  disjoint x y
  disjoint P x
  disjoint P y
  assert |- ( ph -> E. x e. P E. y e. P x =/= y )

  proof
    wph
    cP
    cvv
    wcel
    c2
    cP
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
    cP
    wrex
    vx
    cP
    wrex
    cP
    cG
    cbs
    cfv
    cvv
    tglowdim1.p
    cG
    cbs
    fvex
    eqeltri
    tglowdim1.1
    vx
    vy
    cP
    cvv
    hashge2el2dif
    sylancr
end
