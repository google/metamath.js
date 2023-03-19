include "cushgr.mm"
include "wcel.mm"
include "cuhgr.mm"
include "ushgruhgr.mm"
include "syl.mm"
include "uhgrunop.mm"

theorem ushgrunop
  let wph: wff ph
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cV: class V
  assume ushgrun.g: |- ( ph -> G e. USHGraph )
  assume ushgrun.h: |- ( ph -> H e. USHGraph )
  assume ushgrun.e: |- E = ( iEdg ` G )
  assume ushgrun.f: |- F = ( iEdg ` H )
  assume ushgrun.vg: |- V = ( Vtx ` G )
  assume ushgrun.vh: |- ( ph -> ( Vtx ` H ) = V )
  assume ushgrun.i: |- ( ph -> ( dom E i^i dom F ) = (/) )


  assert |- ( ph -> <. V , ( E u. F ) >. e. UHGraph )

  proof
    wph
    cE
    cF
    cG
    cH
    cV
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
    uhgrunop
end
