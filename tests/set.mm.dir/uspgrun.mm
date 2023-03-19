include "cuspgr.mm"
include "wcel.mm"
include "cupgr.mm"
include "uspgrupgr.mm"
include "syl.mm"
include "upgrun.mm"

theorem uspgrun
  let wph: wff ph
  let cU: class U
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cV: class V
  let cW: class W
  assume uspgrun.g: |- ( ph -> G e. USPGraph )
  assume uspgrun.h: |- ( ph -> H e. USPGraph )
  assume uspgrun.e: |- E = ( iEdg ` G )
  assume uspgrun.f: |- F = ( iEdg ` H )
  assume uspgrun.vg: |- V = ( Vtx ` G )
  assume uspgrun.vh: |- ( ph -> ( Vtx ` H ) = V )
  assume uspgrun.i: |- ( ph -> ( dom E i^i dom F ) = (/) )
  assume uspgrun.u: |- ( ph -> U e. W )
  assume uspgrun.v: |- ( ph -> ( Vtx ` U ) = V )
  assume uspgrun.un: |- ( ph -> ( iEdg ` U ) = ( E u. F ) )


  assert |- ( ph -> U e. UPGraph )

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
    cuspgr
    wcel
    cG
    cupgr
    wcel
    uspgrun.g
    cG
    uspgrupgr
    syl
    wph
    cH
    cuspgr
    wcel
    cH
    cupgr
    wcel
    uspgrun.h
    cH
    uspgrupgr
    syl
    uspgrun.e
    uspgrun.f
    uspgrun.vg
    uspgrun.vh
    uspgrun.i
    uspgrun.u
    uspgrun.v
    uspgrun.un
    upgrun
end
