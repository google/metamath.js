include "cuhgr.mm"
include "wcel.mm"
include "csubgr.mm"
include "wbr.mm"
include "uhgrspansubgr.mm"
include "subuhgr.mm"
include "syl2anc.mm"

theorem uhgrspan
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cE: class E
  let cG: class G
  let cV: class V
  let cW: class W
  let ve: setvar e
  let vi: setvar i
  assume uhgrspan.v: |- V = ( Vtx ` G )
  assume uhgrspan.e: |- E = ( iEdg ` G )
  assume uhgrspan.s: |- ( ph -> S e. W )
  assume uhgrspan.q: |- ( ph -> ( Vtx ` S ) = V )
  assume uhgrspan.r: |- ( ph -> ( iEdg ` S ) = ( E |` A ) )
  assume uhgrspan.g: |- ( ph -> G e. UHGraph )


  assert |- ( ph -> S e. UHGraph )

  proof
    wph
    cG
    cuhgr
    wcel
    cS
    cG
    csubgr
    wbr
    cS
    cuhgr
    wcel
    uhgrspan.g
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
    uhgrspan.g
    uhgrspansubgr
    cS
    cG
    subuhgr
    syl2anc
end
