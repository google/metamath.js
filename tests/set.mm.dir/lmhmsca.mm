include "clmhm.mm"
include "co.mm"
include "wcel.mm"
include "clmod.mm"
include "wa.mm"
include "cghm.mm"
include "wceq.mm"
include "lmhmlem.mm"
include "simprrd.mm"

theorem lmhmsca
  let cS: class S
  let cT: class T
  let cF: class F
  let cK: class K
  let cL: class L
  let va: setvar a
  let vb: setvar b
  assume lmhmlem.k: |- K = ( Scalar ` S )
  assume lmhmlem.l: |- L = ( Scalar ` T )


  assert |- ( F e. ( S LMHom T ) -> L = K )

  proof
    cF
    cS
    cT
    clmhm
    co
    wcel
    cS
    clmod
    wcel
    cT
    clmod
    wcel
    wa
    cF
    cS
    cT
    cghm
    co
    wcel
    cL
    cK
    wceq
    cS
    cT
    cF
    cK
    cL
    lmhmlem.k
    lmhmlem.l
    lmhmlem
    simprrd
end
