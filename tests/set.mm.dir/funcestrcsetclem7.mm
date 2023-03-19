include "wcel.mm"
include "wa.mm"
include "ccid.mm"
include "cfv.mm"
include "co.mm"
include "cid.mm"
include "cbs.mm"
include "cres.mm"
include "cmap.mm"
include "wceq.mm"
include "eqid.mm"
include "funcestrcsetclem5.mm"
include "anabsan2.mm"
include "cwun.mm"
include "adantr.mm"
include "estrcbas.mm"
include "syl6reqr.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "estrcid.mm"
include "fveq12d.mm"
include "cvv.mm"
include "fvex.mm"
include "pm3.2i.mm"
include "a1i.mm"
include "wf.mm"
include "wf1o.mm"
include "f1oi.mm"
include "f1of.mm"
include "ax-mp.mm"
include "elmapg.mm"
include "mpbiri.mm"
include "fvresi.mm"
include "3syl.mm"
include "funcestrcsetclem1.mm"
include "fveq2d.mm"
include "estrcbasbas.mm"
include "setcid.mm"
include "eqtr2d.mm"
include "3eqtrd.mm"

theorem funcestrcsetclem7
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let cS: class S
  let cU: class U
  let cE: class E
  let cF: class F
  let cG: class G
  let cX: class X
  assume funcestrcsetc.e: |- E = ( ExtStrCat ` U )
  assume funcestrcsetc.s: |- S = ( SetCat ` U )
  assume funcestrcsetc.b: |- B = ( Base ` E )
  assume funcestrcsetc.c: |- C = ( Base ` S )
  assume funcestrcsetc.u: |- ( ph -> U e. WUni )
  assume funcestrcsetc.f: |- ( ph -> F = ( x e. B |-> ( Base ` x ) ) )
  assume funcestrcsetc.g: |- ( ph -> G = ( x e. B , y e. B |-> ( _I |` ( ( Base ` y ) ^m ( Base ` x ) ) ) ) )

  disjoint B x
  disjoint X x
  disjoint ph x
  disjoint C x
  disjoint B y
  disjoint x y
  disjoint X y
  disjoint ph y
  assert |- ( ( ph /\ X e. B ) -> ( ( X G X ) ` ( ( Id ` E ) ` X ) ) = ( ( Id ` S ) ` ( F ` X ) ) )

  proof
    wph
    cX
    cB
    wcel
    #
    wa
    #
    cX
    cE
    ccid
    cfv
    #
    cfv
    #
    cX
    cX
    cG
    co
    #
    cfv
    cid
    cX
    cbs
    cfv
    #
    cres
    #
    cid
    @5
    @5
    cmap
    co
    #
    cres
    #
    cfv
    #
    @6
    cX
    cF
    cfv
    #
    cS
    ccid
    cfv
    #
    cfv
    #
    @1
    @3
    @6
    @4
    @8
    wph
    @0
    @4
    @8
    wceq
    wph
    vx
    vy
    cB
    cC
    cS
    cU
    cE
    cF
    cG
    @5
    @5
    cX
    cX
    funcestrcsetc.e
    funcestrcsetc.s
    funcestrcsetc.b
    funcestrcsetc.c
    funcestrcsetc.u
    funcestrcsetc.f
    funcestrcsetc.g
    @5
    eqid
    #
    @13
    funcestrcsetclem5
    anabsan2
    @1
    cE
    cU
    @2
    cwun
    cX
    funcestrcsetc.e
    @2
    eqid
    wph
    cU
    cwun
    wcel
    @0
    funcestrcsetc.u
    adantr
    #
    wph
    @0
    cX
    cU
    wcel
    wph
    cB
    cU
    cX
    wph
    cU
    cE
    cbs
    cfv
    cB
    wph
    cE
    cU
    cwun
    funcestrcsetc.e
    funcestrcsetc.u
    estrcbas
    funcestrcsetc.b
    syl6reqr
    eleq2d
    biimpa
    estrcid
    fveq12d
    @1
    @5
    cvv
    wcel
    #
    @15
    wa
    #
    @6
    @7
    wcel
    #
    @9
    @6
    wceq
    @16
    @1
    @15
    @15
    cX
    cbs
    fvex
    #
    @18
    pm3.2i
    a1i
    @16
    @17
    @5
    @5
    @6
    wf
    #
    @5
    @5
    @6
    wf1o
    @19
    @5
    f1oi
    @5
    @5
    @6
    f1of
    ax-mp
    @5
    @5
    @6
    cvv
    cvv
    elmapg
    mpbiri
    @7
    @6
    fvresi
    3syl
    @1
    @12
    @5
    @11
    cfv
    @6
    @1
    @10
    @5
    @11
    wph
    vx
    cB
    cC
    cS
    cU
    cE
    cF
    cX
    funcestrcsetc.e
    funcestrcsetc.s
    funcestrcsetc.b
    funcestrcsetc.c
    funcestrcsetc.u
    funcestrcsetc.f
    funcestrcsetclem1
    fveq2d
    @1
    cS
    cU
    @11
    cwun
    @5
    funcestrcsetc.s
    @11
    eqid
    @14
    wph
    cB
    cE
    cU
    cX
    funcestrcsetc.e
    funcestrcsetc.b
    funcestrcsetc.u
    estrcbasbas
    setcid
    eqtr2d
    3eqtrd
end
