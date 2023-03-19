include "cvtxdg.mm"
include "cfv.mm"
include "cxad.mm"
include "co.mm"
include "caddc.mm"
include "vtxdun.mm"
include "cdm.mm"
include "cfn.mm"
include "wcel.mm"
include "cn0.mm"
include "eqid.mm"
include "vtxdgfisnn0.mm"
include "syl2anc.mm"
include "nn0red.mm"
include "cvtx.mm"
include "eleqtrrd.mm"
include "rexaddd.mm"
include "eqtrd.mm"

theorem vtxdfiun
  let wph: wff ph
  let cU: class U
  let cG: class G
  let cH: class H
  let cI: class I
  let cJ: class J
  let cN: class N
  let cV: class V
  let vx: setvar x
  assume vtxdun.i: |- I = ( iEdg ` G )
  assume vtxdun.j: |- J = ( iEdg ` H )
  assume vtxdun.vg: |- V = ( Vtx ` G )
  assume vtxdun.vh: |- ( ph -> ( Vtx ` H ) = V )
  assume vtxdun.vu: |- ( ph -> ( Vtx ` U ) = V )
  assume vtxdun.d: |- ( ph -> ( dom I i^i dom J ) = (/) )
  assume vtxdun.fi: |- ( ph -> Fun I )
  assume vtxdun.fj: |- ( ph -> Fun J )
  assume vtxdun.n: |- ( ph -> N e. V )
  assume vtxdun.u: |- ( ph -> ( iEdg ` U ) = ( I u. J ) )
  assume vtxdfiun.a: |- ( ph -> dom I e. Fin )
  assume vtxdfiun.b: |- ( ph -> dom J e. Fin )


  assert |- ( ph -> ( ( VtxDeg ` U ) ` N ) = ( ( ( VtxDeg ` G ) ` N ) + ( ( VtxDeg ` H ) ` N ) ) )

  proof
    wph
    cN
    cU
    cvtxdg
    cfv
    cfv
    cN
    cG
    cvtxdg
    cfv
    cfv
    #
    cN
    cH
    cvtxdg
    cfv
    cfv
    #
    cxad
    co
    @0
    @1
    caddc
    co
    wph
    cU
    cG
    cH
    cI
    cJ
    cN
    cV
    vtxdun.i
    vtxdun.j
    vtxdun.vg
    vtxdun.vh
    vtxdun.vu
    vtxdun.d
    vtxdun.fi
    vtxdun.fj
    vtxdun.n
    vtxdun.u
    vtxdun
    wph
    @0
    @1
    wph
    @0
    wph
    cI
    cdm
    #
    cfn
    wcel
    cN
    cV
    wcel
    @0
    cn0
    wcel
    vtxdfiun.a
    vtxdun.n
    @2
    cN
    cG
    cI
    cV
    vtxdun.vg
    vtxdun.i
    @2
    eqid
    vtxdgfisnn0
    syl2anc
    nn0red
    wph
    @1
    wph
    cJ
    cdm
    #
    cfn
    wcel
    cN
    cH
    cvtx
    cfv
    #
    wcel
    @1
    cn0
    wcel
    vtxdfiun.b
    wph
    cN
    cV
    @4
    vtxdun.n
    vtxdun.vh
    eleqtrrd
    @3
    cN
    cH
    cJ
    @4
    @4
    eqid
    vtxdun.j
    @3
    eqid
    vtxdgfisnn0
    syl2anc
    nn0red
    rexaddd
    eqtrd
end
