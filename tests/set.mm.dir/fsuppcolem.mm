include "ccom.mm"
include "ccnv.mm"
include "cvv.mm"
include "csn.mm"
include "cdif.mm"
include "cima.mm"
include "cfn.mm"
include "cnvco.mm"
include "imaeq1i.mm"
include "imaco.mm"
include "eqtri.mm"
include "wfun.mm"
include "wcel.mm"
include "wf1.mm"
include "wf.mm"
include "df-f1.mm"
include "simprbi.mm"
include "syl.mm"
include "imafi.mm"
include "syl2anc.mm"
include "syl5eqel.mm"

theorem fsuppcolem
  let wph: wff ph
  let cF: class F
  let cG: class G
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume fsuppcolem.f: |- ( ph -> ( `' F " ( _V \ { Z } ) ) e. Fin )
  assume fsuppcolem.g: |- ( ph -> G : X -1-1-> Y )


  assert |- ( ph -> ( `' ( F o. G ) " ( _V \ { Z } ) ) e. Fin )

  proof
    wph
    cF
    cG
    ccom
    ccnv
    #
    cvv
    cZ
    csn
    cdif
    #
    cima
    #
    cG
    ccnv
    #
    cF
    ccnv
    #
    @1
    cima
    #
    cima
    #
    cfn
    @2
    @3
    @4
    ccom
    #
    @1
    cima
    @6
    @0
    @7
    @1
    cF
    cG
    cnvco
    imaeq1i
    @3
    @4
    @1
    imaco
    eqtri
    wph
    @3
    wfun
    #
    @5
    cfn
    wcel
    @6
    cfn
    wcel
    wph
    cX
    cY
    cG
    wf1
    #
    @8
    fsuppcolem.g
    @9
    cX
    cY
    cG
    wf
    @8
    cX
    cY
    cG
    df-f1
    simprbi
    syl
    fsuppcolem.f
    @3
    @5
    imafi
    syl2anc
    syl5eqel
end
