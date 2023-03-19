include "cfusgr.mm"
include "wcel.mm"
include "cupgr.mm"
include "cfn.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "csu.mm"
include "c2.mm"
include "chash.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "fusgrfupgrfs.mm"
include "finsumvtxdg2size.mm"
include "syl.mm"

theorem fusgr1th
  let vv: setvar v
  let cD: class D
  let cG: class G
  let cI: class I
  let cV: class V
  let ve: setvar e
  let vk: setvar k
  let vn: setvar n
  let vf: setvar f
  let vi: setvar i
  let vw: setvar w
  let vy: setvar y
  assume sumvtxdg2size.v: |- V = ( Vtx ` G )
  assume sumvtxdg2size.i: |- I = ( iEdg ` G )
  assume sumvtxdg2size.d: |- D = ( VtxDeg ` G )

  disjoint G v
  disjoint V v
  disjoint G e
  disjoint G k
  disjoint G n
  disjoint e k
  disjoint e n
  disjoint e v
  disjoint k n
  disjoint k v
  disjoint n v
  disjoint e f
  disjoint e i
  disjoint e w
  disjoint f i
  disjoint f k
  disjoint f n
  disjoint f v
  disjoint f w
  disjoint i k
  disjoint i n
  disjoint i v
  disjoint i w
  disjoint k w
  disjoint n w
  disjoint v w
  disjoint e y
  disjoint f y
  disjoint k y
  disjoint n y
  disjoint v y
  disjoint w y
  assert |- ( G e. FinUSGraph -> sum_ v e. V ( D ` v ) = ( 2 x. ( # ` I ) ) )

  proof
    cG
    cfusgr
    wcel
    cG
    cupgr
    wcel
    cV
    cfn
    wcel
    cI
    cfn
    wcel
    w3a
    cV
    vv
    cv
    cD
    cfv
    vv
    csu
    c2
    cI
    chash
    cfv
    cmul
    co
    wceq
    cG
    cI
    cV
    sumvtxdg2size.v
    sumvtxdg2size.i
    fusgrfupgrfs
    vv
    cD
    cG
    cI
    cV
    sumvtxdg2size.v
    sumvtxdg2size.i
    sumvtxdg2size.d
    finsumvtxdg2size
    syl
end
