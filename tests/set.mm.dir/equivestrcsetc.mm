include "cfth.mm"
include "co.mm"
include "wbr.mm"
include "cful.mm"
include "cv.mm"
include "cfv.mm"
include "wf1o.mm"
include "wex.mm"
include "wrex.mm"
include "wral.mm"
include "fthestrcsetc.mm"
include "fullestrcsetc.mm"
include "wcel.mm"
include "wa.mm"
include "cnx.mm"
include "cbs.mm"
include "cop.mm"
include "csn.mm"
include "cwun.mm"
include "setcbas.mm"
include "syl6reqr.mm"
include "eleq2d.mm"
include "eqid.mm"
include "1strwunbndx.mm"
include "ex.mm"
include "sylbid.mm"
include "imp.mm"
include "wceq.mm"
include "estrcbas.mm"
include "adantr.mm"
include "eleqtrrd.mm"
include "wb.mm"
include "fveq2.mm"
include "f1oeq3d.mm"
include "exbidv.mm"
include "adantl.mm"
include "cid.mm"
include "cres.mm"
include "f1oi.mm"
include "funcestrcsetclem1.mm"
include "syldan.mm"
include "1strbas.mm"
include "eqtr4d.mm"
include "mpbiri.mm"
include "cvv.mm"
include "vex.mm"
include "resiexg.mm"
include "ax-mp.mm"
include "f1oeq1.mm"
include "spcev.mm"
include "syl.mm"
include "rspcedvd.mm"
include "ralrimiva.mm"
include "3jca.mm"

theorem equivestrcsetc
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let cS: class S
  let cU: class U
  let vi: setvar i
  let cE: class E
  let cF: class F
  let cG: class G
  let va: setvar a
  let vb: setvar b
  let cX: class X
  let vf: setvar f
  let cY: class Y
  let cZ: class Z
  let vc: setvar c
  let vh: setvar h
  let vk: setvar k
  assume funcestrcsetc.e: |- E = ( ExtStrCat ` U )
  assume funcestrcsetc.s: |- S = ( SetCat ` U )
  assume funcestrcsetc.b: |- B = ( Base ` E )
  assume funcestrcsetc.c: |- C = ( Base ` S )
  assume funcestrcsetc.u: |- ( ph -> U e. WUni )
  assume funcestrcsetc.f: |- ( ph -> F = ( x e. B |-> ( Base ` x ) ) )
  assume funcestrcsetc.g: |- ( ph -> G = ( x e. B , y e. B |-> ( _I |` ( ( Base ` y ) ^m ( Base ` x ) ) ) ) )
  assume equivestrcsetc.i: |- ( ph -> ( Base ` ndx ) e. U )

  disjoint B x
  disjoint ph x
  disjoint C x
  disjoint B y
  disjoint x y
  disjoint ph y
  disjoint a b
  disjoint a x
  disjoint a y
  disjoint b x
  disjoint b y
  disjoint B a
  disjoint B b
  disjoint F a
  disjoint F b
  disjoint G a
  disjoint G b
  disjoint E a
  disjoint E b
  disjoint S a
  disjoint S b
  disjoint a ph
  disjoint b ph
  disjoint C a
  disjoint F i
  disjoint a i
  disjoint b i
  disjoint X x
  disjoint X y
  disjoint B f
  disjoint F f
  disjoint X f
  disjoint Y f
  disjoint Y x
  disjoint Y y
  disjoint f ph
  disjoint Z x
  disjoint Z y
  disjoint a c
  disjoint b c
  disjoint c x
  disjoint c y
  disjoint B c
  disjoint B h
  disjoint B k
  disjoint a h
  disjoint a k
  disjoint b h
  disjoint b k
  disjoint c h
  disjoint c k
  disjoint h k
  disjoint F c
  disjoint F h
  disjoint F k
  disjoint G c
  disjoint G h
  disjoint G k
  disjoint E c
  disjoint E h
  disjoint E k
  disjoint S c
  disjoint S h
  disjoint S k
  disjoint c ph
  disjoint h ph
  disjoint k ph
  assert |- ( ph -> ( F ( E Faith S ) G /\ F ( E Full S ) G /\ A. b e. C E. a e. B E. i i : b -1-1-onto-> ( F ` a ) ) )

  proof
    wph
    cF
    cG
    cE
    cS
    cfth
    co
    wbr
    cF
    cG
    cE
    cS
    cful
    co
    wbr
    vb
    cv
    #
    va
    cv
    #
    cF
    cfv
    #
    vi
    cv
    #
    wf1o
    #
    vi
    wex
    #
    va
    cB
    wrex
    #
    vb
    cC
    wral
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
    funcestrcsetc.e
    funcestrcsetc.s
    funcestrcsetc.b
    funcestrcsetc.c
    funcestrcsetc.u
    funcestrcsetc.f
    funcestrcsetc.g
    fthestrcsetc
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
    funcestrcsetc.e
    funcestrcsetc.s
    funcestrcsetc.b
    funcestrcsetc.c
    funcestrcsetc.u
    funcestrcsetc.f
    funcestrcsetc.g
    fullestrcsetc
    wph
    @6
    vb
    cC
    wph
    @0
    cC
    wcel
    #
    wa
    #
    @5
    @0
    cnx
    cbs
    cfv
    @0
    cop
    csn
    #
    cF
    cfv
    #
    @3
    wf1o
    #
    vi
    wex
    #
    va
    @9
    cB
    @8
    @9
    cU
    cB
    wph
    @7
    @9
    cU
    wcel
    #
    wph
    @7
    @0
    cU
    wcel
    #
    @13
    wph
    cC
    cU
    @0
    wph
    cU
    cS
    cbs
    cfv
    cC
    wph
    cS
    cU
    cwun
    funcestrcsetc.s
    funcestrcsetc.u
    setcbas
    funcestrcsetc.c
    syl6reqr
    eleq2d
    wph
    @14
    @13
    wph
    @0
    cU
    @9
    @9
    eqid
    #
    funcestrcsetc.u
    equivestrcsetc.i
    1strwunbndx
    ex
    sylbid
    imp
    @8
    cU
    cE
    cbs
    cfv
    #
    cB
    wph
    cU
    @16
    wceq
    @7
    wph
    cE
    cU
    cwun
    funcestrcsetc.e
    funcestrcsetc.u
    estrcbas
    adantr
    funcestrcsetc.b
    syl6reqr
    eleqtrrd
    #
    @1
    @9
    wceq
    #
    @5
    @12
    wb
    @8
    @18
    @4
    @11
    vi
    @18
    @2
    @10
    @0
    @3
    @1
    @9
    cF
    fveq2
    f1oeq3d
    exbidv
    adantl
    @8
    @0
    @10
    cid
    @0
    cres
    #
    wf1o
    #
    @12
    @8
    @20
    @0
    @0
    @19
    wf1o
    @0
    f1oi
    @8
    @10
    @0
    @0
    @19
    @8
    @10
    @9
    cbs
    cfv
    #
    @0
    wph
    @7
    @9
    cB
    wcel
    @10
    @21
    wceq
    @17
    wph
    vx
    cB
    cC
    cS
    cU
    cE
    cF
    @9
    funcestrcsetc.e
    funcestrcsetc.s
    funcestrcsetc.b
    funcestrcsetc.c
    funcestrcsetc.u
    funcestrcsetc.f
    funcestrcsetclem1
    syldan
    @7
    @0
    @21
    wceq
    wph
    @0
    @9
    cC
    @15
    1strbas
    adantl
    eqtr4d
    f1oeq3d
    mpbiri
    @11
    @20
    vi
    @19
    @0
    cvv
    wcel
    @19
    cvv
    wcel
    vb
    vex
    @0
    cvv
    resiexg
    ax-mp
    @0
    @10
    @3
    @19
    f1oeq1
    spcev
    syl
    rspcedvd
    ralrimiva
    3jca
end
