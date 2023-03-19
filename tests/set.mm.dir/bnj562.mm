include "w-bnj15.mm"
include "bnj556.mm"
include "syl3an3.mm"

theorem bnj562
  let wta: wff ta
  let wet: wff et
  let wsi: wff si
  let cA: class A
  let cD: class D
  let cR: class R
  let vm: setvar m
  let vn: setvar n
  let vp: setvar p
  let bnjwphn: wff ph"
  assume bnj562.18: |- ( si <-> ( m e. D /\ n = suc m /\ p e. m ) )
  assume bnj562.19: |- ( et <-> ( m e. D /\ n = suc m /\ p e. _om /\ m = suc p ) )
  assume bnj562.38: |- ( ( R _FrSe A /\ ta /\ si ) -> ph" )


  assert |- ( ( R _FrSe A /\ ta /\ et ) -> ph" )

  proof
    wet
    cA
    cR
    w-bnj15
    wta
    wsi
    bnjwphn
    wet
    wsi
    cD
    vm
    vn
    vp
    bnj562.18
    bnj562.19
    bnj556
    bnj562.38
    syl3an3
end
