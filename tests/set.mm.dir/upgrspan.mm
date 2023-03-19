include "cupgr.mm"
include "wcel.mm"
include "csubgr.mm"
include "wbr.mm"
include "cuhgr.mm"
include "upgruhgr.mm"
include "syl.mm"
include "uhgrspansubgr.mm"
include "subupgr.mm"
include "syl2anc.mm"

theorem upgrspan
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
  assume upgrspan.g: |- ( ph -> G e. UPGraph )


  assert |- ( ph -> S e. UPGraph )

  proof
    wph
    cG
    cupgr
    wcel
    #
    cS
    cG
    csubgr
    wbr
    cS
    cupgr
    wcel
    upgrspan.g
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
    upgrspan.g
    cG
    upgruhgr
    syl
    uhgrspansubgr
    cS
    cG
    subupgr
    syl2anc
end
