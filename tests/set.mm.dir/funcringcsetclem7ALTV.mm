include "wcel.mm"
include "wa.mm"
include "ccid.mm"
include "cfv.mm"
include "co.mm"
include "cid.mm"
include "cbs.mm"
include "cres.mm"
include "crh.mm"
include "wceq.mm"
include "funcringcsetclem5ALTV.mm"
include "anabsan2.mm"
include "cwun.mm"
include "eqid.mm"
include "adantr.mm"
include "simpr.mm"
include "ringcidALTV.mm"
include "fveq12d.mm"
include "crg.mm"
include "cin.mm"
include "ringcbasALTV.mm"
include "eleq2d.mm"
include "elin.mm"
include "simprbi.mm"
include "syl6bi.mm"
include "imp.mm"
include "idrhm.mm"
include "fvresi.mm"
include "3syl.mm"
include "funcringcsetclem1ALTV.mm"
include "fveq2d.mm"
include "ringcbasbasALTV.mm"
include "setcid.mm"
include "eqtr2d.mm"
include "3eqtrd.mm"

theorem funcringcsetclem7ALTV
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
  disjoint ph y
  disjoint Y x
  disjoint Y y
  disjoint k x
  assert |- ( ( ph /\ X e. B ) -> ( ( X G X ) ` ( ( Id ` R ) ` X ) ) = ( ( Id ` S ) ` ( F ` X ) ) )

  proof
    wph
    cX
    cB
    wcel
    #
    wa
    #
    cX
    cR
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
    cX
    cX
    crh
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
    cR
    cS
    cU
    cF
    cG
    cX
    cX
    funcringcsetcALTV.r
    funcringcsetcALTV.s
    funcringcsetcALTV.b
    funcringcsetcALTV.c
    funcringcsetcALTV.u
    funcringcsetcALTV.f
    funcringcsetcALTV.g
    funcringcsetclem5ALTV
    anabsan2
    @1
    cB
    cR
    @5
    cU
    @2
    cwun
    cX
    funcringcsetcALTV.r
    funcringcsetcALTV.b
    @2
    eqid
    wph
    cU
    cwun
    wcel
    @0
    funcringcsetcALTV.u
    adantr
    #
    wph
    @0
    simpr
    @5
    eqid
    #
    ringcidALTV
    fveq12d
    @1
    cX
    crg
    wcel
    #
    @6
    @7
    wcel
    @9
    @6
    wceq
    wph
    @0
    @15
    wph
    @0
    cX
    cU
    crg
    cin
    #
    wcel
    #
    @15
    wph
    cB
    @16
    cX
    wph
    cB
    cR
    cU
    cwun
    funcringcsetcALTV.r
    funcringcsetcALTV.b
    funcringcsetcALTV.u
    ringcbasALTV
    eleq2d
    @17
    cX
    cU
    wcel
    @15
    cX
    cU
    crg
    elin
    simprbi
    syl6bi
    imp
    @5
    cX
    @14
    idrhm
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
    cR
    cS
    cU
    cF
    cX
    funcringcsetcALTV.r
    funcringcsetcALTV.s
    funcringcsetcALTV.b
    funcringcsetcALTV.c
    funcringcsetcALTV.u
    funcringcsetcALTV.f
    funcringcsetclem1ALTV
    fveq2d
    @1
    cS
    cU
    @11
    cwun
    @5
    funcringcsetcALTV.s
    @11
    eqid
    @13
    wph
    cB
    cR
    cX
    cU
    funcringcsetcALTV.r
    funcringcsetcALTV.b
    funcringcsetcALTV.u
    ringcbasbasALTV
    setcid
    eqtr2d
    3eqtrd
end
