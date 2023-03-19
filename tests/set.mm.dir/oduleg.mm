include "wbr.mm"
include "ccnv.mm"
include "wcel.mm"
include "wa.mm"
include "cple.mm"
include "cfv.mm"
include "oduleval.mm"
include "eqtr4i.mm"
include "breqi.mm"
include "brcnvg.mm"
include "syl5bb.mm"

theorem oduleg
  let cA: class A
  let cB: class B
  let cD: class D
  let cG: class G
  let c.le: class .<_
  let cO: class O
  let cV: class V
  let cW: class W
  let va: setvar a
  assume oduval.d: |- D = ( ODual ` O )
  assume oduval.l: |- .<_ = ( le ` O )
  assume oduleg.g: |- G = ( le ` D )


  assert |- ( ( A e. V /\ B e. W ) -> ( A G B <-> B .<_ A ) )

  proof
    cA
    cB
    cG
    wbr
    cA
    cB
    c.le
    ccnv
    #
    wbr
    cA
    cV
    wcel
    cB
    cW
    wcel
    wa
    cB
    cA
    c.le
    wbr
    cA
    cB
    cG
    @0
    cG
    cD
    cple
    cfv
    @0
    oduleg.g
    cD
    c.le
    cO
    oduval.d
    oduval.l
    oduleval
    eqtr4i
    breqi
    cA
    cB
    cV
    cW
    c.le
    brcnvg
    syl5bb
end
