include "wcel.mm"
include "wa.mm"
include "cmap.mm"
include "co.mm"
include "w3a.mm"
include "cfv.mm"
include "cid.mm"
include "cres.mm"
include "wceq.mm"
include "funcestrcsetclem5.mm"
include "3adant3.mm"
include "fveq1d.mm"
include "fvresi.mm"
include "3ad2ant3.mm"
include "eqtrd.mm"

theorem funcestrcsetclem6
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
  let cH: class H
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y
  assume funcestrcsetc.e: |- E = ( ExtStrCat ` U )
  assume funcestrcsetc.s: |- S = ( SetCat ` U )
  assume funcestrcsetc.b: |- B = ( Base ` E )
  assume funcestrcsetc.c: |- C = ( Base ` S )
  assume funcestrcsetc.u: |- ( ph -> U e. WUni )
  assume funcestrcsetc.f: |- ( ph -> F = ( x e. B |-> ( Base ` x ) ) )
  assume funcestrcsetc.g: |- ( ph -> G = ( x e. B , y e. B |-> ( _I |` ( ( Base ` y ) ^m ( Base ` x ) ) ) ) )
  assume funcestrcsetc.m: |- M = ( Base ` X )
  assume funcestrcsetc.n: |- N = ( Base ` Y )

  disjoint M x
  disjoint M y
  disjoint x y
  disjoint N x
  disjoint N y
  disjoint Y x
  disjoint Y y
  disjoint B x
  disjoint X x
  disjoint ph x
  disjoint C x
  disjoint B y
  disjoint x y
  disjoint X y
  disjoint ph y
  assert |- ( ( ph /\ ( X e. B /\ Y e. B ) /\ H e. ( N ^m M ) ) -> ( ( X G Y ) ` H ) = H )

  proof
    wph
    cX
    cB
    wcel
    cY
    cB
    wcel
    wa
    #
    cH
    cN
    cM
    cmap
    co
    #
    wcel
    #
    w3a
    #
    cH
    cX
    cY
    cG
    co
    #
    cfv
    cH
    cid
    @1
    cres
    #
    cfv
    #
    cH
    @3
    cH
    @4
    @5
    wph
    @0
    @4
    @5
    wceq
    @2
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
    cM
    cN
    cX
    cY
    funcestrcsetc.e
    funcestrcsetc.s
    funcestrcsetc.b
    funcestrcsetc.c
    funcestrcsetc.u
    funcestrcsetc.f
    funcestrcsetc.g
    funcestrcsetc.m
    funcestrcsetc.n
    funcestrcsetclem5
    3adant3
    fveq1d
    @2
    wph
    @6
    cH
    wceq
    @0
    @1
    cH
    fvresi
    3ad2ant3
    eqtrd
end
