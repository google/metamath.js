include "wcel.mm"
include "wa.mm"
include "crh.mm"
include "co.mm"
include "w3a.mm"
include "cfv.mm"
include "cid.mm"
include "cres.mm"
include "wceq.mm"
include "funcringcsetclem5ALTV.mm"
include "3adant3.mm"
include "fveq1d.mm"
include "fvresi.mm"
include "3ad2ant3.mm"
include "eqtrd.mm"

theorem funcringcsetclem6ALTV
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cU: class U
  let cF: class F
  let cG: class G
  let cH: class H
  let cX: class X
  let cY: class Y
  let vk: setvar k
  assume funcringcsetcALTV.r: |- R = ( RingCatALTV ` U )
  assume funcringcsetcALTV.s: |- S = ( SetCat ` U )
  assume funcringcsetcALTV.b: |- B = ( Base ` R )
  assume funcringcsetcALTV.c: |- C = ( Base ` S )
  assume funcringcsetcALTV.u: |- ( ph -> U e. WUni )
  assume funcringcsetcALTV.f: |- ( ph -> F = ( x e. B |-> ( Base ` x ) ) )
  assume funcringcsetcALTV.g: |- ( ph -> G = ( x e. B , y e. B |-> ( _I |` ( x RingHom y ) ) ) )

  disjoint B x
  disjoint X x
  disjoint ph x
  disjoint C x
  disjoint B y
  disjoint x y
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint ph y
  disjoint k x
  assert |- ( ( ph /\ ( X e. B /\ Y e. B ) /\ H e. ( X RingHom Y ) ) -> ( ( X G Y ) ` H ) = H )

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
    cX
    cY
    crh
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
    cR
    cS
    cU
    cF
    cG
    cX
    cY
    funcringcsetcALTV.r
    funcringcsetcALTV.s
    funcringcsetcALTV.b
    funcringcsetcALTV.c
    funcringcsetcALTV.u
    funcringcsetcALTV.f
    funcringcsetcALTV.g
    funcringcsetclem5ALTV
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
