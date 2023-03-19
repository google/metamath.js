include "wcel.mm"
include "wa.mm"
include "cid.mm"
include "cv.mm"
include "crh.mm"
include "co.mm"
include "cres.mm"
include "cvv.mm"
include "cmpt2.mm"
include "wceq.mm"
include "adantr.mm"
include "oveq12.mm"
include "adantl.mm"
include "reseq2d.mm"
include "simprl.mm"
include "simprr.mm"
include "ovexd.mm"
include "resiexd.mm"
include "ovmpt2d.mm"

theorem funcringcsetcALTV2lem5
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
  let cX: class X
  let cY: class Y
  let vk: setvar k
  assume funcringcsetcALTV2.r: |- R = ( RingCat ` U )
  assume funcringcsetcALTV2.s: |- S = ( SetCat ` U )
  assume funcringcsetcALTV2.b: |- B = ( Base ` R )
  assume funcringcsetcALTV2.c: |- C = ( Base ` S )
  assume funcringcsetcALTV2.u: |- ( ph -> U e. WUni )
  assume funcringcsetcALTV2.f: |- ( ph -> F = ( x e. B |-> ( Base ` x ) ) )
  assume funcringcsetcALTV2.g: |- ( ph -> G = ( x e. B , y e. B |-> ( _I |` ( x RingHom y ) ) ) )

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
  assert |- ( ( ph /\ ( X e. B /\ Y e. B ) ) -> ( X G Y ) = ( _I |` ( X RingHom Y ) ) )

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
    vx
    cv
    #
    vy
    cv
    #
    crh
    co
    #
    cres
    #
    cid
    cX
    cY
    crh
    co
    #
    cres
    cG
    cvv
    wph
    cG
    vx
    vy
    cB
    cB
    @7
    cmpt2
    wceq
    @2
    funcringcsetcALTV2.g
    adantr
    @3
    @4
    cX
    wceq
    @5
    cY
    wceq
    wa
    #
    wa
    @6
    @8
    cid
    @9
    @6
    @8
    wceq
    @3
    @4
    cX
    @5
    cY
    crh
    oveq12
    adantl
    reseq2d
    wph
    @0
    @1
    simprl
    wph
    @0
    @1
    simprr
    @3
    @8
    cvv
    @3
    cX
    cY
    crh
    ovexd
    resiexd
    ovmpt2d
end
