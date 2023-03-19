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
include "uhgrun.mm"

theorem uhgrunop
  let wph: wff ph
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cV: class V
  assume uhgrun.g: |- ( ph -> G e. UHGraph )
  assume uhgrun.h: |- ( ph -> H e. UHGraph )
  assume uhgrun.e: |- E = ( iEdg ` G )
  assume uhgrun.f: |- F = ( iEdg ` H )
  assume uhgrun.vg: |- V = ( Vtx ` G )
  assume uhgrun.vh: |- ( ph -> ( Vtx ` H ) = V )
  assume uhgrun.i: |- ( ph -> ( dom E i^i dom F ) = (/) )


  assert |- ( ph -> <. V , ( E u. F ) >. e. UHGraph )

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
    uhgrun.g
    uhgrun.h
    uhgrun.e
    uhgrun.f
    uhgrun.vg
    uhgrun.vh
    uhgrun.i
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
    uhgrun.vg
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
    uhgrun.e
    cG
    ciedg
    fvex
    eqeltri
    cF
    cH
    ciedg
    cfv
    cvv
    uhgrun.f
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
    uhgrun
end
