include "wcel.mm"
include "wa.mm"
include "cid.mm"
include "cv.mm"
include "cbs.mm"
include "cfv.mm"
include "cmap.mm"
include "co.mm"
include "cres.mm"
include "cvv.mm"
include "cmpt2.mm"
include "wceq.mm"
include "adantr.mm"
include "fveq2.mm"
include "oveqan12rd.mm"
include "oveq12i.mm"
include "syl6eqr.mm"
include "reseq2d.mm"
include "adantl.mm"
include "simprl.mm"
include "simprr.mm"
include "ovexd.mm"
include "resiexd.mm"
include "ovmpt2d.mm"

theorem funcestrcsetclem5
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
  assert |- ( ( ph /\ ( X e. B /\ Y e. B ) ) -> ( X G Y ) = ( _I |` ( N ^m M ) ) )

  proof
    wph
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    wa
    #
    wa
    #
    vx
    vy
    cX
    cY
    cB
    cB
    cid
    vy
    cv
    #
    cbs
    cfv
    #
    vx
    cv
    #
    cbs
    cfv
    #
    cmap
    co
    #
    cres
    #
    cid
    cN
    cM
    cmap
    co
    #
    cres
    #
    cG
    cvv
    wph
    cG
    vx
    vy
    cB
    cB
    @9
    cmpt2
    wceq
    @2
    funcestrcsetc.g
    adantr
    @6
    cX
    wceq
    #
    @4
    cY
    wceq
    #
    wa
    #
    @9
    @11
    wceq
    @3
    @14
    @8
    @10
    cid
    @14
    @8
    cY
    cbs
    cfv
    #
    cX
    cbs
    cfv
    #
    cmap
    co
    @10
    @13
    @12
    @5
    @15
    @7
    @16
    cmap
    @4
    cY
    cbs
    fveq2
    @6
    cX
    cbs
    fveq2
    oveqan12rd
    cN
    @15
    cM
    @16
    cmap
    funcestrcsetc.n
    funcestrcsetc.m
    oveq12i
    syl6eqr
    reseq2d
    adantl
    wph
    @0
    @1
    simprl
    wph
    @0
    @1
    simprr
    @3
    @10
    cvv
    @3
    cN
    cM
    cmap
    ovexd
    resiexd
    ovmpt2d
end
