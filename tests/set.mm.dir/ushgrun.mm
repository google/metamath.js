include "cushgr.mm"
include "wcel.mm"
include "cuhgr.mm"
include "ushgruhgr.mm"
include "syl.mm"
include "uhgrun.mm"

theorem ushgrun
  let wph: wff ph
  let cU: class U
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cV: class V
  let cW: class W
  assume ushgrun.g: |- ( ph -> G e. USHGraph )
  assume ushgrun.h: |- ( ph -> H e. USHGraph )
  assume ushgrun.e: |- E = ( iEdg ` G )
  assume ushgrun.f: |- F = ( iEdg ` H )
  assume ushgrun.vg: |- V = ( Vtx ` G )
  assume ushgrun.vh: |- ( ph -> ( Vtx ` H ) = V )
  assume ushgrun.i: |- ( ph -> ( dom E i^i dom F ) = (/) )
  assume ushgrun.u: |- ( ph -> U e. W )
  assume ushgrun.v: |- ( ph -> ( Vtx ` U ) = V )
  assume ushgrun.un: |- ( ph -> ( iEdg ` U ) = ( E u. F ) )


  assert |- ( ph -> U e. UHGraph )

  proof
    wph
    cU
    cE
    cF
    cG
    cH
    cV
    cW
    wph
    cG
    cushgr
    wcel
    cG
    cuhgr
    wcel
    ushgrun.g
    cG
    ushgruhgr
    syl
    wph
    cH
    cushgr
    wcel
    cH
    cuhgr
    wcel
    ushgrun.h
    cH
    ushgruhgr
    syl
    ushgrun.e
    ushgrun.f
    ushgrun.vg
    ushgrun.vh
    ushgrun.i
    ushgrun.u
    ushgrun.v
    ushgrun.un
    uhgrun
end
