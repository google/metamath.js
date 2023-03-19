include "cringc.mm"
include "cfv.mm"
include "cestrc.mm"
include "cresc.mm"
include "co.mm"
include "cv.mm"
include "crh.mm"
include "crg.mm"
include "cin.mm"
include "cxp.mm"
include "cres.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "df-ringc.mm"
include "a1i.mm"
include "wa.mm"
include "fveq2.mm"
include "adantl.mm"
include "ineq1.mm"
include "sqxpeqd.mm"
include "eqcomd.mm"
include "sylan9eqr.mm"
include "reseq2d.mm"
include "adantr.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "wcel.mm"
include "elex.mm"
include "syl.mm"
include "ovexd.mm"
include "fvmptd.mm"
include "syl5eq.mm"

theorem ringcval
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cU: class U
  let cH: class H
  let cV: class V
  let vu: setvar u
  let vk: setvar k
  let vx: setvar x
  assume ringcval.c: |- C = ( RingCat ` U )
  assume ringcval.u: |- ( ph -> U e. V )
  assume ringcval.b: |- ( ph -> B = ( U i^i Ring ) )
  assume ringcval.h: |- ( ph -> H = ( RingHom |` ( B X. B ) ) )


  assert |- ( ph -> C = ( ( ExtStrCat ` U ) |`cat H ) )

  proof
    wph
    cC
    cU
    cringc
    cfv
    cU
    cestrc
    cfv
    #
    cH
    cresc
    co
    #
    ringcval.c
    wph
    vu
    cU
    vu
    cv
    #
    cestrc
    cfv
    #
    crh
    @2
    crg
    cin
    #
    @4
    cxp
    #
    cres
    #
    cresc
    co
    #
    @1
    cvv
    cringc
    cvv
    cringc
    vu
    cvv
    @7
    cmpt
    wceq
    wph
    vu
    df-ringc
    a1i
    wph
    @2
    cU
    wceq
    #
    wa
    #
    @3
    @0
    @6
    cH
    cresc
    @8
    @3
    @0
    wceq
    wph
    @2
    cU
    cestrc
    fveq2
    adantl
    @9
    @6
    crh
    cB
    cB
    cxp
    #
    cres
    #
    cH
    @9
    @5
    @10
    crh
    @8
    wph
    @5
    cU
    crg
    cin
    #
    @12
    cxp
    #
    @10
    @8
    @4
    @12
    @2
    cU
    crg
    ineq1
    sqxpeqd
    wph
    @10
    @13
    wph
    cB
    @12
    ringcval.b
    sqxpeqd
    eqcomd
    sylan9eqr
    reseq2d
    wph
    @11
    cH
    wceq
    @8
    wph
    cH
    @11
    ringcval.h
    eqcomd
    adantr
    eqtrd
    oveq12d
    wph
    cU
    cV
    wcel
    cU
    cvv
    wcel
    ringcval.u
    cU
    cV
    elex
    syl
    wph
    @0
    cH
    cresc
    ovexd
    fvmptd
    syl5eq
end
