include "w-bnj15.mm"
include "cv.mm"
include "wfn.mm"
include "bnj556.mm"
include "syl3an3.mm"

theorem bnj561
  let wta: wff ta
  let wet: wff et
  let wsi: wff si
  let cA: class A
  let cD: class D
  let cR: class R
  let vm: setvar m
  let vn: setvar n
  let cG: class G
  let vp: setvar p
  assume bnj561.18: |- ( si <-> ( m e. D /\ n = suc m /\ p e. m ) )
  assume bnj561.19: |- ( et <-> ( m e. D /\ n = suc m /\ p e. _om /\ m = suc p ) )
  assume bnj561.37: |- ( ( R _FrSe A /\ ta /\ si ) -> G Fn n )


  assert |- ( ( R _FrSe A /\ ta /\ et ) -> G Fn n )

  proof
    wet
    cA
    cR
    w-bnj15
    wta
    wsi
    cG
    vn
    cv
    wfn
    wet
    wsi
    cD
    vm
    vn
    vp
    bnj561.18
    bnj561.19
    bnj556
    bnj561.37
    syl3an3
end
