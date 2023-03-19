include "cusgr.mm"
include "wcel.mm"
include "cumgr.mm"
include "usgrumgr.mm"
include "syl.mm"
include "umgrun.mm"

theorem usgrun
  let wph: wff ph
  let cU: class U
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cV: class V
  let cW: class W
  assume usgrun.g: |- ( ph -> G e. USGraph )
  assume usgrun.h: |- ( ph -> H e. USGraph )
  assume usgrun.e: |- E = ( iEdg ` G )
  assume usgrun.f: |- F = ( iEdg ` H )
  assume usgrun.vg: |- V = ( Vtx ` G )
  assume usgrun.vh: |- ( ph -> ( Vtx ` H ) = V )
  assume usgrun.i: |- ( ph -> ( dom E i^i dom F ) = (/) )
  assume usgrun.u: |- ( ph -> U e. W )
  assume usgrun.v: |- ( ph -> ( Vtx ` U ) = V )
  assume usgrun.un: |- ( ph -> ( iEdg ` U ) = ( E u. F ) )


  assert |- ( ph -> U e. UMGraph )

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
    cusgr
    wcel
    cG
    cumgr
    wcel
    usgrun.g
    cG
    usgrumgr
    syl
    wph
    cH
    cusgr
    wcel
    cH
    cumgr
    wcel
    usgrun.h
    cH
    usgrumgr
    syl
    usgrun.e
    usgrun.f
    usgrun.vg
    usgrun.vh
    usgrun.i
    usgrun.u
    usgrun.v
    usgrun.un
    umgrun
end
