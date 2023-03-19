include "cfv.mm"
include "c1st.mm"
include "c2nd.mm"
include "cop.mm"
include "ccom.mm"
include "co.mm"
include "cxp.mm"
include "wcel.mm"
include "wceq.mm"
include "ffvelrnd.mm"
include "1st2nd2.mm"
include "syl.mm"
include "fveq2d.mm"
include "wf.mm"
include "fvco3.mm"
include "syl2anc.mm"
include "df-ov.mm"
include "a1i.mm"
include "3eqtr4d.mm"

theorem fvovco
  let wph: wff ph
  let cF: class F
  let cO: class O
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume fvovco.1: |- ( ph -> F : X --> ( V X. W ) )
  assume fvovco.2: |- ( ph -> Y e. X )


  assert |- ( ph -> ( ( O o. F ) ` Y ) = ( ( 1st ` ( F ` Y ) ) O ( 2nd ` ( F ` Y ) ) ) )

  proof
    wph
    cY
    cF
    cfv
    #
    cO
    cfv
    #
    @0
    c1st
    cfv
    #
    @0
    c2nd
    cfv
    #
    cop
    #
    cO
    cfv
    #
    cY
    cO
    cF
    ccom
    cfv
    #
    @2
    @3
    cO
    co
    #
    wph
    @0
    @4
    cO
    wph
    @0
    cV
    cW
    cxp
    #
    wcel
    @0
    @4
    wceq
    wph
    cX
    @8
    cY
    cF
    fvovco.1
    fvovco.2
    ffvelrnd
    @0
    cV
    cW
    1st2nd2
    syl
    fveq2d
    wph
    cX
    @8
    cF
    wf
    cY
    cX
    wcel
    @6
    @1
    wceq
    fvovco.1
    fvovco.2
    cX
    @8
    cY
    cO
    cF
    fvco3
    syl2anc
    @7
    @5
    wceq
    wph
    @2
    @3
    cO
    df-ov
    a1i
    3eqtr4d
end
