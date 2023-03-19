include "cuhgr.mm"
include "wcel.mm"
include "wfun.mm"
include "uhgrfun.mm"
include "syl.mm"
include "vtxdfiun.mm"

theorem vtxduhgrfiun
  let wph: wff ph
  let cU: class U
  let cG: class G
  let cH: class H
  let cI: class I
  let cJ: class J
  let cN: class N
  let cV: class V
  assume vtxduhgrun.i: |- I = ( iEdg ` G )
  assume vtxduhgrun.j: |- J = ( iEdg ` H )
  assume vtxduhgrun.vg: |- V = ( Vtx ` G )
  assume vtxduhgrun.vh: |- ( ph -> ( Vtx ` H ) = V )
  assume vtxduhgrun.vu: |- ( ph -> ( Vtx ` U ) = V )
  assume vtxduhgrun.d: |- ( ph -> ( dom I i^i dom J ) = (/) )
  assume vtxduhgrun.g: |- ( ph -> G e. UHGraph )
  assume vtxduhgrun.h: |- ( ph -> H e. UHGraph )
  assume vtxduhgrun.n: |- ( ph -> N e. V )
  assume vtxduhgrun.u: |- ( ph -> ( iEdg ` U ) = ( I u. J ) )
  assume vtxduhgrfiun.a: |- ( ph -> dom I e. Fin )
  assume vtxduhgrfiun.b: |- ( ph -> dom J e. Fin )


  assert |- ( ph -> ( ( VtxDeg ` U ) ` N ) = ( ( ( VtxDeg ` G ) ` N ) + ( ( VtxDeg ` H ) ` N ) ) )

  proof
    wph
    cU
    cG
    cH
    cI
    cJ
    cN
    cV
    vtxduhgrun.i
    vtxduhgrun.j
    vtxduhgrun.vg
    vtxduhgrun.vh
    vtxduhgrun.vu
    vtxduhgrun.d
    wph
    cG
    cuhgr
    wcel
    cI
    wfun
    vtxduhgrun.g
    cI
    cG
    vtxduhgrun.i
    uhgrfun
    syl
    wph
    cH
    cuhgr
    wcel
    cJ
    wfun
    vtxduhgrun.h
    cJ
    cH
    vtxduhgrun.j
    uhgrfun
    syl
    vtxduhgrun.n
    vtxduhgrun.u
    vtxduhgrfiun.a
    vtxduhgrfiun.b
    vtxdfiun
end
