include "co.mm"
include "wbr.mm"
include "chom.mm"
include "cfv.mm"
include "wcel.mm"
include "cop.mm"
include "cco.mm"
include "ccid.mm"
include "wceq.mm"
include "w3a.mm"
include "crh.mm"
include "ccom.mm"
include "cid.mm"
include "cres.mm"
include "eqid.mm"
include "ccat.mm"
include "ringccatALTV.mm"
include "syl.mm"
include "issect.mm"
include "wa.mm"
include "ringchomALTV.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "anbi1d.mm"
include "adantr.mm"
include "simprl.mm"
include "simprr.mm"
include "ringccoALTV.mm"
include "ringcidALTV.mm"
include "eqeq12d.mm"
include "pm5.32da.mm"
include "bitrd.mm"
include "df-3an.mm"
include "3bitr4g.mm"

theorem ringcsectALTV
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cS: class S
  let cU: class U
  let cE: class E
  let cF: class F
  let cG: class G
  let cV: class V
  let cX: class X
  let cY: class Y
  let vk: setvar k
  let vx: setvar x
  assume ringcsectALTV.c: |- C = ( RingCatALTV ` U )
  assume ringcsectALTV.b: |- B = ( Base ` C )
  assume ringcsectALTV.u: |- ( ph -> U e. V )
  assume ringcsectALTV.x: |- ( ph -> X e. B )
  assume ringcsectALTV.y: |- ( ph -> Y e. B )
  assume ringcsectALTV.e: |- E = ( Base ` X )
  assume ringcsectALTV.n: |- S = ( Sect ` C )


  assert |- ( ph -> ( F ( X S Y ) G <-> ( F e. ( X RingHom Y ) /\ G e. ( Y RingHom X ) /\ ( G o. F ) = ( _I |` E ) ) ) )

  proof
    wph
    cF
    cG
    cX
    cY
    cS
    co
    wbr
    cF
    cX
    cY
    cC
    chom
    cfv
    #
    co
    #
    wcel
    #
    cG
    cY
    cX
    @0
    co
    #
    wcel
    #
    cG
    cF
    cX
    cY
    cop
    cX
    cC
    cco
    cfv
    #
    co
    co
    #
    cX
    cC
    ccid
    cfv
    #
    cfv
    #
    wceq
    #
    w3a
    #
    cF
    cX
    cY
    crh
    co
    #
    wcel
    #
    cG
    cY
    cX
    crh
    co
    #
    wcel
    #
    cG
    cF
    ccom
    #
    cid
    cE
    cres
    #
    wceq
    #
    w3a
    #
    wph
    cB
    cC
    cS
    @5
    @7
    cF
    cG
    @0
    cX
    cY
    ringcsectALTV.b
    @0
    eqid
    #
    @5
    eqid
    #
    @7
    eqid
    #
    ringcsectALTV.n
    wph
    cU
    cV
    wcel
    #
    cC
    ccat
    wcel
    ringcsectALTV.u
    cC
    cU
    cV
    ringcsectALTV.c
    ringccatALTV
    syl
    ringcsectALTV.x
    ringcsectALTV.y
    issect
    wph
    @2
    @4
    wa
    #
    @9
    wa
    #
    @12
    @14
    wa
    #
    @17
    wa
    #
    @10
    @18
    wph
    @24
    @25
    @9
    wa
    @26
    wph
    @23
    @25
    @9
    wph
    @2
    @12
    @4
    @14
    wph
    @1
    @11
    cF
    wph
    cB
    cC
    cU
    @0
    cV
    cX
    cY
    ringcsectALTV.c
    ringcsectALTV.b
    ringcsectALTV.u
    @19
    ringcsectALTV.x
    ringcsectALTV.y
    ringchomALTV
    eleq2d
    wph
    @3
    @13
    cG
    wph
    cB
    cC
    cU
    @0
    cV
    cY
    cX
    ringcsectALTV.c
    ringcsectALTV.b
    ringcsectALTV.u
    @19
    ringcsectALTV.y
    ringcsectALTV.x
    ringchomALTV
    eleq2d
    anbi12d
    anbi1d
    wph
    @25
    @9
    @17
    wph
    @25
    wa
    #
    @6
    @15
    @8
    @16
    @27
    cB
    cC
    @5
    cU
    cF
    cG
    cV
    cX
    cY
    cX
    ringcsectALTV.c
    ringcsectALTV.b
    wph
    @22
    @25
    ringcsectALTV.u
    adantr
    @20
    wph
    cX
    cB
    wcel
    @25
    ringcsectALTV.x
    adantr
    #
    wph
    cY
    cB
    wcel
    @25
    ringcsectALTV.y
    adantr
    @28
    wph
    @12
    @14
    simprl
    wph
    @12
    @14
    simprr
    ringccoALTV
    wph
    @8
    @16
    wceq
    @25
    wph
    cB
    cC
    cE
    cU
    @7
    cV
    cX
    ringcsectALTV.c
    ringcsectALTV.b
    @21
    ringcsectALTV.u
    ringcsectALTV.x
    ringcsectALTV.e
    ringcidALTV
    adantr
    eqeq12d
    pm5.32da
    bitrd
    @2
    @4
    @9
    df-3an
    @12
    @14
    @17
    df-3an
    3bitr4g
    bitrd
end
