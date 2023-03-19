include "cuspgr.mm"
include "wcel.mm"
include "cupgr.mm"
include "uspgrupgr.mm"
include "syl.mm"
include "upgrunop.mm"

theorem uspgrunop
  let wph: wff ph
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cV: class V
  assume uspgrun.g: |- ( ph -> G e. USPGraph )
  assume uspgrun.h: |- ( ph -> H e. USPGraph )
  assume uspgrun.e: |- E = ( iEdg ` G )
  assume uspgrun.f: |- F = ( iEdg ` H )
  assume uspgrun.vg: |- V = ( Vtx ` G )
  assume uspgrun.vh: |- ( ph -> ( Vtx ` H ) = V )
  assume uspgrun.i: |- ( ph -> ( dom E i^i dom F ) = (/) )


  assert |- ( ph -> <. V , ( E u. F ) >. e. UPGraph )

  proof
    wph
    cE
    cF
    cG
    cH
    cV
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
    upgrunop
end
