include "cicc.mm"
include "co.mm"
include "cima.mm"
include "clt.mm"
include "wiso.mm"
include "crn.mm"
include "cres.mm"
include "cv.mm"
include "wbr.mm"
include "cfv.mm"
include "wi.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "ex.mm"
include "ralrimivva.mm"
include "wor.mm"
include "cr.mm"
include "wf.mm"
include "wss.mm"
include "wb.mm"
include "iccssre.mm"
include "syl2anc.mm"
include "ltso.mm"
include "soss.mm"
include "mpisyl.mm"
include "a1i.mm"
include "ccncf.mm"
include "cncff.mm"
include "syl.mm"
include "ssid.mm"
include "soisores.mm"
include "syl22anc.mm"
include "mpbird.mm"
include "wfn.mm"
include "wceq.mm"
include "ffn.mm"
include "3syl.mm"
include "fnresdm.mm"
include "isoeq1.mm"
include "mpbid.mm"
include "fnima.mm"
include "isoeq5.mm"

theorem dvgt0lem2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cS: class S
  let cF: class F
  let cO: class O
  let vz: setvar z
  let cX: class X
  let cY: class Y
  assume dvgt0.a: |- ( ph -> A e. RR )
  assume dvgt0.b: |- ( ph -> B e. RR )
  assume dvgt0.f: |- ( ph -> F e. ( ( A [,] B ) -cn-> RR ) )
  assume dvgt0lem.d: |- ( ph -> ( RR _D F ) : ( A (,) B ) --> S )
  assume dvgt0lem.o: |- O Or RR
  assume dvgt0lem.i: |- ( ( ( ph /\ ( x e. ( A [,] B ) /\ y e. ( A [,] B ) ) ) /\ x < y ) -> ( F ` x ) O ( F ` y ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint O x
  disjoint O y
  disjoint ph x
  disjoint ph y
  disjoint B x
  disjoint B y
  disjoint F x
  disjoint F y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint ph z
  disjoint S z
  disjoint X z
  disjoint Y z
  disjoint B z
  disjoint F z
  assert |- ( ph -> F Isom < , O ( ( A [,] B ) , ran F ) )

  proof
    wph
    cA
    cB
    cicc
    co
    #
    cF
    @0
    cima
    #
    clt
    cO
    cF
    wiso
    #
    @0
    cF
    crn
    #
    clt
    cO
    cF
    wiso
    #
    wph
    @0
    @1
    clt
    cO
    cF
    @0
    cres
    #
    wiso
    #
    @2
    wph
    @6
    vx
    cv
    #
    vy
    cv
    #
    clt
    wbr
    #
    @7
    cF
    cfv
    @8
    cF
    cfv
    cO
    wbr
    #
    wi
    #
    vy
    @0
    wral
    vx
    @0
    wral
    #
    wph
    @11
    vx
    vy
    @0
    @0
    wph
    @7
    @0
    wcel
    @8
    @0
    wcel
    wa
    wa
    @9
    @10
    dvgt0lem.i
    ex
    ralrimivva
    wph
    @0
    clt
    wor
    #
    cr
    cO
    wor
    #
    @0
    cr
    cF
    wf
    #
    @0
    @0
    wss
    #
    @6
    @12
    wb
    wph
    @0
    cr
    wss
    #
    cr
    clt
    wor
    @13
    wph
    cA
    cr
    wcel
    cB
    cr
    wcel
    @17
    dvgt0.a
    dvgt0.b
    cA
    cB
    iccssre
    syl2anc
    ltso
    @0
    cr
    clt
    soss
    mpisyl
    @14
    wph
    dvgt0lem.o
    a1i
    wph
    cF
    @0
    cr
    ccncf
    co
    wcel
    #
    @15
    dvgt0.f
    @0
    cr
    cF
    cncff
    #
    syl
    @16
    wph
    @0
    ssid
    a1i
    vx
    vy
    @0
    @0
    cr
    clt
    cO
    cF
    soisores
    syl22anc
    mpbird
    wph
    cF
    @0
    wfn
    #
    @5
    cF
    wceq
    @6
    @2
    wb
    wph
    @18
    @15
    @20
    dvgt0.f
    @19
    @0
    cr
    cF
    ffn
    3syl
    #
    @0
    cF
    fnresdm
    @0
    @1
    clt
    cO
    cF
    @5
    isoeq1
    3syl
    mpbid
    wph
    @20
    @1
    @3
    wceq
    @2
    @4
    wb
    @21
    @0
    cF
    fnima
    @0
    @1
    @3
    clt
    cO
    cF
    isoeq5
    3syl
    mpbid
end
