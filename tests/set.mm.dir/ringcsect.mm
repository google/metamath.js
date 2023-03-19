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
include "ringccat.mm"
include "syl.mm"
include "issect.mm"
include "wa.mm"
include "ringchom.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "anbi1d.mm"
include "adantr.mm"
include "wi.mm"
include "crg.mm"
include "cin.mm"
include "ringcbas.mm"
include "wss.mm"
include "inss1.mm"
include "a1i.mm"
include "sseld.mm"
include "sylbid.mm"
include "mpd.mm"
include "cbs.mm"
include "wf.mm"
include "rhmf.mm"
include "adantl.mm"
include "ringcco.mm"
include "ringcid.mm"
include "eqeq12d.mm"
include "pm5.32da.mm"
include "bitrd.mm"
include "df-3an.mm"
include "3bitr4g.mm"

theorem ringcsect
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
  assume ringcsect.c: |- C = ( RingCat ` U )
  assume ringcsect.b: |- B = ( Base ` C )
  assume ringcsect.u: |- ( ph -> U e. V )
  assume ringcsect.x: |- ( ph -> X e. B )
  assume ringcsect.y: |- ( ph -> Y e. B )
  assume ringcsect.e: |- E = ( Base ` X )
  assume ringcsect.n: |- S = ( Sect ` C )


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
    ringcsect.b
    @0
    eqid
    #
    @5
    eqid
    #
    @7
    eqid
    #
    ringcsect.n
    wph
    cU
    cV
    wcel
    #
    cC
    ccat
    wcel
    ringcsect.u
    cC
    cU
    cV
    ringcsect.c
    ringccat
    syl
    ringcsect.x
    ringcsect.y
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
    ringcsect.c
    ringcsect.b
    ringcsect.u
    @19
    ringcsect.x
    ringcsect.y
    ringchom
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
    ringcsect.c
    ringcsect.b
    ringcsect.u
    @19
    ringcsect.y
    ringcsect.x
    ringchom
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
    cC
    @5
    cU
    cF
    cG
    cV
    cX
    cY
    cX
    ringcsect.c
    wph
    @22
    @25
    ringcsect.u
    adantr
    @20
    @27
    cX
    cB
    wcel
    #
    cX
    cU
    wcel
    #
    wph
    @28
    @25
    ringcsect.x
    adantr
    wph
    @28
    @29
    wi
    @25
    wph
    @28
    cX
    cU
    crg
    cin
    #
    wcel
    @29
    wph
    cB
    @30
    cX
    wph
    cB
    cC
    cU
    cV
    ringcsect.c
    ringcsect.b
    ringcsect.u
    ringcbas
    #
    eleq2d
    wph
    @30
    cU
    cX
    @30
    cU
    wss
    wph
    cU
    crg
    inss1
    a1i
    #
    sseld
    sylbid
    adantr
    mpd
    #
    @27
    cY
    cB
    wcel
    #
    cY
    cU
    wcel
    #
    wph
    @34
    @25
    ringcsect.y
    adantr
    wph
    @34
    @35
    wi
    @25
    wph
    @34
    cY
    @30
    wcel
    @35
    wph
    cB
    @30
    cY
    @31
    eleq2d
    wph
    @30
    cU
    cY
    @32
    sseld
    sylbid
    adantr
    mpd
    @33
    @25
    cX
    cbs
    cfv
    #
    cY
    cbs
    cfv
    #
    cF
    wf
    #
    wph
    @12
    @38
    @14
    @36
    @37
    cX
    cY
    cF
    @36
    eqid
    #
    @37
    eqid
    #
    rhmf
    adantr
    adantl
    @25
    @37
    @36
    cG
    wf
    #
    wph
    @14
    @41
    @12
    @37
    @36
    cY
    cX
    cG
    @40
    @39
    rhmf
    adantl
    adantl
    ringcco
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
    ringcsect.c
    ringcsect.b
    @21
    ringcsect.u
    ringcsect.x
    ringcsect.e
    ringcid
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
