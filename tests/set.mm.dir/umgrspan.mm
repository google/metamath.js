include "cumgr.mm"
include "wcel.mm"
include "csubgr.mm"
include "wbr.mm"
include "cuhgr.mm"
include "umgruhgr.mm"
include "syl.mm"
include "uhgrspansubgr.mm"
include "subumgr.mm"
include "syl2anc.mm"

theorem umgrspan
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
  assume umgrspan.g: |- ( ph -> G e. UMGraph )


  assert |- ( ph -> S e. UMGraph )

  proof
    wph
    cG
    cumgr
    wcel
    #
    cS
    cG
    csubgr
    wbr
    cS
    cumgr
    wcel
    umgrspan.g
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
    umgrspan.g
    cG
    umgruhgr
    syl
    uhgrspansubgr
    cS
    cG
    subumgr
    syl2anc
end
