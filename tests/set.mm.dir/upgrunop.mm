include "cun.mm"
include "cop.mm"
include "cvv.mm"
include "wcel.mm"
include "opex.mm"
include "a1i.mm"
include "wa.mm"
include "cvtx.mm"
include "cfv.mm"
include "wceq.mm"
include "fvex.mm"
include "eqeltri.mm"
include "ciedg.mm"
include "unex.mm"
include "pm3.2i.mm"
include "opvtxfv.mm"
include "mp1i.mm"
include "opiedgfv.mm"
include "upgrun.mm"

theorem upgrunop
  let wph: wff ph
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cV: class V
  assume upgrun.g: |- ( ph -> G e. UPGraph )
  assume upgrun.h: |- ( ph -> H e. UPGraph )
  assume upgrun.e: |- E = ( iEdg ` G )
  assume upgrun.f: |- F = ( iEdg ` H )
  assume upgrun.vg: |- V = ( Vtx ` G )
  assume upgrun.vh: |- ( ph -> ( Vtx ` H ) = V )
  assume upgrun.i: |- ( ph -> ( dom E i^i dom F ) = (/) )


  assert |- ( ph -> <. V , ( E u. F ) >. e. UPGraph )

  proof
    wph
    cV
    cE
    cF
    cun
    #
    cop
    #
    cE
    cF
    cG
    cH
    cV
    cvv
    upgrun.g
    upgrun.h
    upgrun.e
    upgrun.f
    upgrun.vg
    upgrun.vh
    upgrun.i
    @1
    cvv
    wcel
    wph
    cV
    @0
    opex
    a1i
    cV
    cvv
    wcel
    #
    @0
    cvv
    wcel
    #
    wa
    #
    @1
    cvtx
    cfv
    cV
    wceq
    wph
    @2
    @3
    cV
    cG
    cvtx
    cfv
    cvv
    upgrun.vg
    cG
    cvtx
    fvex
    eqeltri
    cE
    cF
    cE
    cG
    ciedg
    cfv
    cvv
    upgrun.e
    cG
    ciedg
    fvex
    eqeltri
    cF
    cH
    ciedg
    cfv
    cvv
    upgrun.f
    cH
    ciedg
    fvex
    eqeltri
    unex
    pm3.2i
    #
    @0
    cV
    cvv
    cvv
    opvtxfv
    mp1i
    @4
    @1
    ciedg
    cfv
    @0
    wceq
    wph
    @5
    @0
    cV
    cvv
    cvv
    opiedgfv
    mp1i
    upgrun
end
