include "wf.mm"
include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "cop.mm"
include "csn.mm"
include "cmpt.mm"
include "wcel.mm"
include "wa.mm"
include "setc1strwun.mm"
include "wceq.mm"
include "cwun.mm"
include "estrcbas.mm"
include "eqcomd.mm"
include "adantr.mm"
include "eleqtrrd.mm"
include "syl6eleqr.mm"
include "eqid.mm"
include "fmptd.mm"
include "feq1d.mm"
include "mpbird.mm"

theorem funcsetcestrclem3
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cC: class C
  let cS: class S
  let cU: class U
  let cE: class E
  let cF: class F
  let cX: class X
  assume funcsetcestrc.s: |- S = ( SetCat ` U )
  assume funcsetcestrc.c: |- C = ( Base ` S )
  assume funcsetcestrc.f: |- ( ph -> F = ( x e. C |-> { <. ( Base ` ndx ) , x >. } ) )
  assume funcsetcestrc.u: |- ( ph -> U e. WUni )
  assume funcsetcestrc.o: |- ( ph -> _om e. U )
  assume funcsetcestrclem3.e: |- E = ( ExtStrCat ` U )
  assume funcsetcestrclem3.b: |- B = ( Base ` E )

  disjoint B x
  disjoint C x
  disjoint C x
  disjoint ph x
  disjoint X x
  assert |- ( ph -> F : C --> B )

  proof
    wph
    cC
    cB
    cF
    wf
    cC
    cB
    vx
    cC
    cnx
    cbs
    cfv
    vx
    cv
    #
    cop
    csn
    #
    cmpt
    #
    wf
    wph
    vx
    cC
    @1
    cB
    @2
    wph
    @0
    cC
    wcel
    #
    wa
    #
    @1
    cE
    cbs
    cfv
    #
    cB
    @4
    @1
    cU
    @5
    wph
    cC
    cS
    cU
    @0
    funcsetcestrc.s
    funcsetcestrc.c
    funcsetcestrc.u
    funcsetcestrc.o
    setc1strwun
    wph
    @5
    cU
    wceq
    @3
    wph
    cU
    @5
    wph
    cE
    cU
    cwun
    funcsetcestrclem3.e
    funcsetcestrc.u
    estrcbas
    eqcomd
    adantr
    eleqtrrd
    funcsetcestrclem3.b
    syl6eleqr
    @2
    eqid
    fmptd
    wph
    cC
    cB
    cF
    @2
    funcsetcestrc.f
    feq1d
    mpbird
end
