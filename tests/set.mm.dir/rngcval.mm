include "crngc.mm"
include "cfv.mm"
include "cestrc.mm"
include "cresc.mm"
include "co.mm"
include "cv.mm"
include "crngh.mm"
include "crng.mm"
include "cin.mm"
include "cxp.mm"
include "cres.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "df-rngc.mm"
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

theorem rngcval
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cU: class U
  let cH: class H
  let cV: class V
  let vu: setvar u
  let vk: setvar k
  let vx: setvar x
  assume rngcval.c: |- C = ( RngCat ` U )
  assume rngcval.u: |- ( ph -> U e. V )
  assume rngcval.b: |- ( ph -> B = ( U i^i Rng ) )
  assume rngcval.h: |- ( ph -> H = ( RngHomo |` ( B X. B ) ) )


  assert |- ( ph -> C = ( ( ExtStrCat ` U ) |`cat H ) )

  proof
    wph
    cC
    cU
    crngc
    cfv
    cU
    cestrc
    cfv
    #
    cH
    cresc
    co
    #
    rngcval.c
    wph
    vu
    cU
    vu
    cv
    #
    cestrc
    cfv
    #
    crngh
    @2
    crng
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
    crngc
    cvv
    crngc
    vu
    cvv
    @7
    cmpt
    wceq
    wph
    vu
    df-rngc
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
    crngh
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
    crngh
    @8
    wph
    @5
    cU
    crng
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
    crng
    ineq1
    sqxpeqd
    wph
    @10
    @13
    wph
    cB
    @12
    rngcval.b
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
    rngcval.h
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
    rngcval.u
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
