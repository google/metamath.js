include "cgsu.mm"
include "co.mm"
include "csb.mm"
include "cbs.mm"
include "cfv.mm"
include "wcel.mm"
include "ralrimivw.mm"
include "gsummpt1n0.mm"
include "wceq.mm"
include "csbconstg.mm"
include "syl.mm"
include "eqtrd.mm"

theorem gsummptif1n0
  let wph: wff ph
  let cA: class A
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cI: class I
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume gsummpt1n0.0: |- .0. = ( 0g ` G )
  assume gsummpt1n0.g: |- ( ph -> G e. Mnd )
  assume gsummpt1n0.i: |- ( ph -> I e. W )
  assume gsummpt1n0.x: |- ( ph -> X e. I )
  assume gsummpt1n0.f: |- F = ( n e. I |-> if ( n = X , A , .0. ) )
  assume gsummptif1n0.a: |- ( ph -> A e. ( Base ` G ) )

  disjoint G n
  disjoint I n
  disjoint X n
  disjoint n ph
  disjoint .0. n
  disjoint A n
  assert |- ( ph -> ( G gsum F ) = A )

  proof
    wph
    cG
    cF
    cgsu
    co
    vn
    cX
    cA
    csb
    #
    cA
    wph
    cA
    vn
    cF
    cG
    cI
    cW
    cX
    c.0
    gsummpt1n0.0
    gsummpt1n0.g
    gsummpt1n0.i
    gsummpt1n0.x
    gsummpt1n0.f
    wph
    cA
    cG
    cbs
    cfv
    wcel
    vn
    cI
    gsummptif1n0.a
    ralrimivw
    gsummpt1n0
    wph
    cX
    cI
    wcel
    @0
    cA
    wceq
    gsummpt1n0.x
    vn
    cX
    cA
    cI
    csbconstg
    syl
    eqtrd
end
