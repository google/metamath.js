include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "wf1.mm"
include "funcsetcestrclem3.mm"
include "wcel.mm"
include "wa.mm"
include "cnx.mm"
include "cbs.mm"
include "cop.mm"
include "csn.mm"
include "funcsetcestrclem1.mm"
include "adantrr.mm"
include "adantrl.mm"
include "eqeq12d.mm"
include "cvv.mm"
include "wb.mm"
include "opex.mm"
include "sneqbg.mm"
include "mp1i.mm"
include "fvexd.mm"
include "simpl.mm"
include "opthg.mm"
include "syl2an.mm"
include "simpr.mm"
include "syl6bi.mm"
include "sylbid.mm"
include "ralrimivva.mm"
include "dff13.mm"
include "sylanbrc.mm"

theorem embedsetcestrclem
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cC: class C
  let cS: class S
  let cU: class U
  let cE: class E
  let cF: class F
  let vy: setvar y
  let vz: setvar z
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
  disjoint ph x
  disjoint C x
  disjoint ph x
  disjoint C y
  disjoint C z
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint ph y
  disjoint ph z
  disjoint x y
  disjoint x z
  disjoint X x
  assert |- ( ph -> F : C -1-1-> B )

  proof
    wph
    cC
    cB
    cF
    wf
    vy
    cv
    #
    cF
    cfv
    #
    vz
    cv
    #
    cF
    cfv
    #
    wceq
    #
    vy
    vz
    weq
    #
    wi
    #
    vz
    cC
    wral
    vy
    cC
    wral
    cC
    cB
    cF
    wf1
    wph
    vx
    cB
    cC
    cS
    cU
    cE
    cF
    funcsetcestrc.s
    funcsetcestrc.c
    funcsetcestrc.f
    funcsetcestrc.u
    funcsetcestrc.o
    funcsetcestrclem3.e
    funcsetcestrclem3.b
    funcsetcestrclem3
    wph
    @6
    vy
    vz
    cC
    cC
    wph
    @0
    cC
    wcel
    #
    @2
    cC
    wcel
    #
    wa
    #
    wa
    #
    @4
    cnx
    cbs
    cfv
    #
    @0
    cop
    #
    csn
    #
    @11
    @2
    cop
    #
    csn
    #
    wceq
    #
    @5
    @10
    @1
    @13
    @3
    @15
    wph
    @7
    @1
    @13
    wceq
    @8
    wph
    vx
    cC
    cS
    cU
    cF
    @0
    funcsetcestrc.s
    funcsetcestrc.c
    funcsetcestrc.f
    funcsetcestrclem1
    adantrr
    wph
    @8
    @3
    @15
    wceq
    @7
    wph
    vx
    cC
    cS
    cU
    cF
    @2
    funcsetcestrc.s
    funcsetcestrc.c
    funcsetcestrc.f
    funcsetcestrclem1
    adantrl
    eqeq12d
    @10
    @16
    @12
    @14
    wceq
    #
    @5
    @12
    cvv
    wcel
    @16
    @17
    wb
    @10
    @11
    @0
    opex
    @12
    @14
    cvv
    sneqbg
    mp1i
    @10
    @17
    @11
    @11
    wceq
    #
    @5
    wa
    #
    @5
    wph
    @11
    cvv
    wcel
    @7
    @17
    @19
    wb
    @9
    wph
    cnx
    cbs
    fvexd
    @7
    @8
    simpl
    @11
    @0
    @11
    @2
    cvv
    cC
    opthg
    syl2an
    @18
    @5
    simpr
    syl6bi
    sylbid
    sylbid
    ralrimivva
    vy
    vz
    cC
    cB
    cF
    dff13
    sylanbrc
end
