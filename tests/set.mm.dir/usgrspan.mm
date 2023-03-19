include "cusgr.mm"
include "wcel.mm"
include "csubgr.mm"
include "wbr.mm"
include "cuhgr.mm"
include "usgruhgr.mm"
include "syl.mm"
include "uhgrspansubgr.mm"
include "subusgr.mm"
include "syl2anc.mm"

theorem usgrspan
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cE: class E
  let cG: class G
  let cV: class V
  let cW: class W
  assume uhgrspan.v: |- V = ( Vtx ` G )
  assume uhgrspan.e: |- E = ( iEdg ` G )
  assume uhgrspan.s: |- ( ph -> S e. W )
  assume uhgrspan.q: |- ( ph -> ( Vtx ` S ) = V )
  assume uhgrspan.r: |- ( ph -> ( iEdg ` S ) = ( E |` A ) )
  assume usgrspan.g: |- ( ph -> G e. USGraph )


  assert |- ( ph -> S e. USGraph )

  proof
    wph
    cG
    cusgr
    wcel
    #
    cS
    cG
    csubgr
    wbr
    cS
    cusgr
    wcel
    usgrspan.g
    wph
    cA
    cS
    cE
    cG
    cV
    cW
    uhgrspan.v
    uhgrspan.e
    uhgrspan.s
    uhgrspan.q
    uhgrspan.r
    wph
    @0
    cG
    cuhgr
    wcel
    usgrspan.g
    cG
    usgruhgr
    syl
    uhgrspansubgr
    cS
    cG
    subusgr
    syl2anc
end
