include "cusgr.mm"
include "wcel.mm"
include "cumgr.mm"
include "usgrumgr.mm"
include "syl.mm"
include "umgrunop.mm"

theorem usgrunop
  let wph: wff ph
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cV: class V
  assume usgrun.g: |- ( ph -> G e. USGraph )
  assume usgrun.h: |- ( ph -> H e. USGraph )
  assume usgrun.e: |- E = ( iEdg ` G )
  assume usgrun.f: |- F = ( iEdg ` H )
  assume usgrun.vg: |- V = ( Vtx ` G )
  assume usgrun.vh: |- ( ph -> ( Vtx ` H ) = V )
  assume usgrun.i: |- ( ph -> ( dom E i^i dom F ) = (/) )


  assert |- ( ph -> <. V , ( E u. F ) >. e. UMGraph )

  proof
    wph
    cE
    cF
    cG
    cH
    cV
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
    umgrunop
end
