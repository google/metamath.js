include "wcel.mm"
include "wa.mm"
include "cfn.mm"
include "w3a.mm"
include "cxp.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "cbs.mm"
include "cfv.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "adantl.mm"
include "3ad2ant1.mm"
include "wceq.mm"
include "simpl.mm"
include "xpfi.mm"
include "anim12i.mm"
include "3adant3.mm"
include "frlmfibas.mm"
include "syl.mm"
include "eleqtrrd.mm"
include "elmapi.mm"
include "simp3l.mm"
include "simp3r.mm"
include "fovrnd.mm"

theorem frlmbas3
  let cB: class B
  let cR: class R
  let cF: class F
  let cI: class I
  let cJ: class J
  let cM: class M
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  assume frlmbas3.f: |- F = ( R freeLMod ( N X. M ) )
  assume frlmbas3.b: |- B = ( Base ` R )
  assume frlmbas3.v: |- V = ( Base ` F )


  assert |- ( ( ( R e. W /\ X e. V ) /\ ( N e. Fin /\ M e. Fin ) /\ ( I e. N /\ J e. M ) ) -> ( I X J ) e. B )

  proof
    cR
    cW
    wcel
    #
    cX
    cV
    wcel
    #
    wa
    #
    cN
    cfn
    wcel
    cM
    cfn
    wcel
    wa
    #
    cI
    cN
    wcel
    #
    cJ
    cM
    wcel
    #
    wa
    #
    w3a
    #
    cI
    cJ
    cB
    cN
    cM
    cX
    @7
    cX
    cB
    cN
    cM
    cxp
    #
    cmap
    co
    #
    wcel
    @8
    cB
    cX
    wf
    @7
    cX
    cF
    cbs
    cfv
    #
    @9
    @2
    @3
    cX
    @10
    wcel
    #
    @6
    @1
    @11
    @0
    @1
    @11
    cV
    @10
    cX
    frlmbas3.v
    eleq2i
    biimpi
    adantl
    3ad2ant1
    @7
    @0
    @8
    cfn
    wcel
    #
    wa
    #
    @9
    @10
    wceq
    @2
    @3
    @13
    @6
    @2
    @0
    @3
    @12
    @0
    @1
    simpl
    cN
    cM
    xpfi
    anim12i
    3adant3
    cR
    cF
    @8
    cB
    cW
    frlmbas3.f
    frlmbas3.b
    frlmfibas
    syl
    eleqtrrd
    cX
    cB
    @8
    elmapi
    syl
    @2
    @3
    @4
    @5
    simp3l
    @2
    @3
    @4
    @5
    simp3r
    fovrnd
end
