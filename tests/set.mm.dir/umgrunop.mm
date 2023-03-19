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
include "umgrun.mm"

theorem umgrunop
  let wph: wff ph
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cV: class V
  assume umgrun.g: |- ( ph -> G e. UMGraph )
  assume umgrun.h: |- ( ph -> H e. UMGraph )
  assume umgrun.e: |- E = ( iEdg ` G )
  assume umgrun.f: |- F = ( iEdg ` H )
  assume umgrun.vg: |- V = ( Vtx ` G )
  assume umgrun.vh: |- ( ph -> ( Vtx ` H ) = V )
  assume umgrun.i: |- ( ph -> ( dom E i^i dom F ) = (/) )


  assert |- ( ph -> <. V , ( E u. F ) >. e. UMGraph )

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
    umgrun.g
    umgrun.h
    umgrun.e
    umgrun.f
    umgrun.vg
    umgrun.vh
    umgrun.i
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
    umgrun.vg
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
    umgrun.e
    cG
    ciedg
    fvex
    eqeltri
    cF
    cH
    ciedg
    cfv
    cvv
    umgrun.f
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
    umgrun
end
