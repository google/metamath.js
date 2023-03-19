include "ctcl.mm"
include "cfv.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "wcel.mm"
include "w3o.mm"
include "wbr.mm"
include "wceq.mm"
include "cun.mm"
include "wrel.mm"
include "wb.mm"
include "cvv.mm"
include "wfun.mm"
include "funrel.mm"
include "syl.mm"
include "reltrclfv.mm"
include "syl2anc.mm"
include "eliniseg2.mm"
include "mpbird.mm"
include "brrelex2.mm"
include "un12.mm"
include "a1i.mm"
include "frege131d.mm"
include "frege83d.mm"
include "wo.mm"
include "elun.mm"
include "orbi2i.mm"
include "3orass.mm"
include "3bitr4i.mm"
include "sylib.mm"
include "biimpd.mm"
include "wi.mm"
include "elsni.mm"
include "elrelimasn.mm"
include "3orim123d.mm"
include "mpd.mm"

theorem frege133d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let cX: class X
  assume frege133d.f: |- ( ph -> F e. _V )
  assume frege133d.xa: |- ( ph -> X ( t+ ` F ) A )
  assume frege133d.xb: |- ( ph -> X ( t+ ` F ) B )
  assume frege133d.fun: |- ( ph -> Fun F )


  assert |- ( ph -> ( A ( t+ ` F ) B \/ A = B \/ B ( t+ ` F ) A ) )

  proof
    wph
    cA
    cF
    ctcl
    cfv
    #
    ccnv
    cB
    csn
    #
    cima
    #
    wcel
    #
    cA
    @1
    wcel
    #
    cA
    @0
    @1
    cima
    #
    wcel
    #
    w3o
    #
    cA
    cB
    @0
    wbr
    #
    cA
    cB
    wceq
    #
    cB
    cA
    @0
    wbr
    #
    w3o
    wph
    cA
    @2
    @1
    @5
    cun
    #
    cun
    #
    wcel
    #
    @7
    wph
    cX
    cA
    cF
    @2
    @11
    frege133d.f
    wph
    cX
    @2
    wcel
    #
    cX
    cB
    @0
    wbr
    #
    frege133d.xb
    wph
    @0
    wrel
    #
    @14
    @15
    wb
    wph
    cF
    cvv
    wcel
    cF
    wrel
    #
    @16
    frege133d.f
    wph
    cF
    wfun
    @17
    frege133d.fun
    cF
    funrel
    syl
    cF
    cvv
    reltrclfv
    syl2anc
    #
    @0
    cB
    cX
    eliniseg2
    syl
    mpbird
    wph
    @16
    cX
    cA
    @0
    wbr
    cA
    cvv
    wcel
    @18
    frege133d.xa
    cX
    cA
    @0
    brrelex2
    syl2anc
    frege133d.xa
    wph
    @12
    @1
    cF
    frege133d.f
    @12
    @1
    @2
    @5
    cun
    cun
    wceq
    wph
    @2
    @1
    @5
    un12
    a1i
    frege133d.fun
    frege131d
    frege83d
    @3
    cA
    @11
    wcel
    #
    wo
    @3
    @4
    @6
    wo
    #
    wo
    @13
    @7
    @19
    @20
    @3
    cA
    @1
    @5
    elun
    orbi2i
    cA
    @2
    @11
    elun
    @3
    @4
    @6
    3orass
    3bitr4i
    sylib
    wph
    @3
    @8
    @4
    @9
    @6
    @10
    wph
    @3
    @8
    wph
    @16
    @3
    @8
    wb
    @18
    @0
    cB
    cA
    eliniseg2
    syl
    biimpd
    @4
    @9
    wi
    wph
    cA
    cB
    elsni
    a1i
    wph
    @6
    @10
    wph
    @16
    @6
    @10
    wb
    @18
    cB
    cA
    @0
    elrelimasn
    syl
    biimpd
    3orim123d
    mpd
end
