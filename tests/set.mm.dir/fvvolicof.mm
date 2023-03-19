include "cvol.mm"
include "cico.mm"
include "ccom.mm"
include "cfv.mm"
include "c1st.mm"
include "c2nd.mm"
include "co.mm"
include "wfun.mm"
include "cdm.mm"
include "wcel.mm"
include "wceq.mm"
include "cxr.mm"
include "cxp.mm"
include "wf.mm"
include "ffun.mm"
include "syl.mm"
include "fdm.mm"
include "eqcomd.mm"
include "eleqtrd.mm"
include "fvco.mm"
include "syl2anc.mm"
include "cpw.mm"
include "icof.mm"
include "ax-mp.mm"
include "a1i.mm"
include "ffvelrnd.mm"
include "fdmi.mm"
include "syl6eleqr.mm"
include "cop.mm"
include "df-ov.mm"
include "1st2nd2.mm"
include "fveq2d.mm"
include "eqtr2d.mm"
include "3eqtrd.mm"

theorem fvvolicof
  let wph: wff ph
  let cA: class A
  let cF: class F
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume fvvolicof.f: |- ( ph -> F : A --> ( RR* X. RR* ) )
  assume fvvolicof.x: |- ( ph -> X e. A )


  assert |- ( ph -> ( ( ( vol o. [,) ) o. F ) ` X ) = ( vol ` ( ( 1st ` ( F ` X ) ) [,) ( 2nd ` ( F ` X ) ) ) ) )

  proof
    wph
    cX
    cvol
    cico
    ccom
    #
    cF
    ccom
    cfv
    #
    cX
    cF
    cfv
    #
    @0
    cfv
    #
    @2
    cico
    cfv
    #
    cvol
    cfv
    #
    @2
    c1st
    cfv
    #
    @2
    c2nd
    cfv
    #
    cico
    co
    #
    cvol
    cfv
    wph
    cF
    wfun
    #
    cX
    cF
    cdm
    #
    wcel
    @1
    @3
    wceq
    wph
    cA
    cxr
    cxr
    cxp
    #
    cF
    wf
    #
    @9
    fvvolicof.f
    cA
    @11
    cF
    ffun
    syl
    wph
    cX
    cA
    @10
    fvvolicof.x
    wph
    @10
    cA
    wph
    @12
    @10
    cA
    wceq
    fvvolicof.f
    cA
    @11
    cF
    fdm
    syl
    eqcomd
    eleqtrd
    cX
    @0
    cF
    fvco
    syl2anc
    wph
    cico
    wfun
    #
    @2
    cico
    cdm
    #
    wcel
    @3
    @5
    wceq
    @13
    wph
    @11
    cxr
    cpw
    #
    cico
    wf
    @13
    icof
    @11
    @15
    cico
    ffun
    ax-mp
    a1i
    wph
    @2
    @11
    @14
    wph
    cA
    @11
    cX
    cF
    fvvolicof.f
    fvvolicof.x
    ffvelrnd
    #
    @11
    @15
    cico
    icof
    fdmi
    syl6eleqr
    @2
    cvol
    cico
    fvco
    syl2anc
    wph
    @4
    @8
    cvol
    wph
    @8
    @6
    @7
    cop
    #
    cico
    cfv
    #
    @4
    @8
    @18
    wceq
    wph
    @6
    @7
    cico
    df-ov
    a1i
    wph
    @17
    @2
    cico
    wph
    @2
    @17
    wph
    @2
    @11
    wcel
    @2
    @17
    wceq
    @16
    @2
    cxr
    cxr
    1st2nd2
    syl
    eqcomd
    fveq2d
    eqtr2d
    fveq2d
    3eqtrd
end
