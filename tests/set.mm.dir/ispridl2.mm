include "crngo.mm"
include "wcel.mm"
include "cidl.mm"
include "cfv.mm"
include "wne.mm"
include "cv.mm"
include "co.mm"
include "wo.mm"
include "wi.mm"
include "wral.mm"
include "w3a.mm"
include "cpridl.mm"
include "wss.mm"
include "wa.mm"
include "idlss.mm"
include "ssralv.mm"
include "syl.mm"
include "adantrr.mm"
include "ralimdv.mm"
include "adantrl.mm"
include "syld.mm"
include "adantlr.mm"
include "r19.26-2.mm"
include "pm3.35.mm"
include "2ralimi.mm"
include "2ralor.mm"
include "dfss3.mm"
include "orbi12i.mm"
include "sylbb2.mm"
include "sylbir.mm"
include "expcom.mm"
include "syl6.mm"
include "ralrimdvva.mm"
include "ex.mm"
include "adantrd.mm"
include "imdistand.mm"
include "df-3an.mm"
include "3imtr4g.mm"
include "ispridl.mm"
include "sylibrd.mm"
include "imp.mm"

theorem ispridl2
  let cP: class P
  let cR: class R
  let cG: class G
  let cH: class H
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vr: setvar r
  let vs: setvar s
  assume ispridl2.1: |- G = ( 1st ` R )
  assume ispridl2.2: |- H = ( 2nd ` R )
  assume ispridl2.3: |- X = ran G

  disjoint R a
  disjoint R b
  disjoint a b
  disjoint P a
  disjoint P b
  disjoint X a
  disjoint X b
  disjoint R r
  disjoint R s
  disjoint a r
  disjoint a s
  disjoint b r
  disjoint b s
  disjoint r s
  disjoint P r
  disjoint P s
  disjoint X r
  disjoint X s
  disjoint H r
  disjoint H s
  assert |- ( ( R e. RingOps /\ ( P e. ( Idl ` R ) /\ P =/= X /\ A. a e. X A. b e. X ( ( a H b ) e. P -> ( a e. P \/ b e. P ) ) ) ) -> P e. ( PrIdl ` R ) )

  proof
    cR
    crngo
    wcel
    #
    cP
    cR
    cidl
    cfv
    #
    wcel
    #
    cP
    cX
    wne
    #
    va
    cv
    #
    vb
    cv
    #
    cH
    co
    cP
    wcel
    #
    @4
    cP
    wcel
    #
    @5
    cP
    wcel
    #
    wo
    #
    wi
    #
    vb
    cX
    wral
    #
    va
    cX
    wral
    #
    w3a
    #
    cP
    cR
    cpridl
    cfv
    wcel
    #
    @0
    @13
    @2
    @3
    @6
    vb
    vs
    cv
    #
    wral
    va
    vr
    cv
    #
    wral
    #
    @16
    cP
    wss
    #
    @15
    cP
    wss
    #
    wo
    #
    wi
    #
    vs
    @1
    wral
    vr
    @1
    wral
    #
    w3a
    #
    @14
    @0
    @2
    @3
    wa
    #
    @12
    wa
    @24
    @22
    wa
    @13
    @23
    @0
    @24
    @12
    @22
    @0
    @2
    @12
    @22
    wi
    #
    @3
    @0
    @2
    @25
    @0
    @2
    wa
    #
    @12
    @21
    vr
    vs
    @1
    @1
    @26
    @16
    @1
    wcel
    #
    @15
    @1
    wcel
    #
    wa
    #
    wa
    @12
    @10
    vb
    @15
    wral
    #
    va
    @16
    wral
    #
    @21
    @0
    @29
    @12
    @31
    wi
    @2
    @0
    @29
    wa
    @12
    @11
    va
    @16
    wral
    #
    @31
    @0
    @27
    @12
    @32
    wi
    #
    @28
    @0
    @27
    wa
    @16
    cX
    wss
    @33
    cR
    cG
    @16
    cX
    ispridl2.1
    ispridl2.3
    idlss
    @11
    va
    @16
    cX
    ssralv
    syl
    adantrr
    @0
    @28
    @32
    @31
    wi
    #
    @27
    @0
    @28
    wa
    @15
    cX
    wss
    #
    @34
    cR
    cG
    @15
    cX
    ispridl2.1
    ispridl2.3
    idlss
    @35
    @11
    @30
    va
    @16
    @10
    vb
    @15
    cX
    ssralv
    ralimdv
    syl
    adantrl
    syld
    adantlr
    @17
    @31
    @20
    @17
    @31
    wa
    @6
    @10
    wa
    #
    vb
    @15
    wral
    va
    @16
    wral
    #
    @20
    @6
    @10
    va
    vb
    @16
    @15
    r19.26-2
    @37
    @9
    vb
    @15
    wral
    va
    @16
    wral
    #
    @20
    @36
    @9
    va
    vb
    @16
    @15
    @6
    @9
    pm3.35
    2ralimi
    @38
    @7
    va
    @16
    wral
    #
    @8
    vb
    @15
    wral
    #
    wo
    @20
    @7
    @8
    va
    vb
    @16
    @15
    2ralor
    @18
    @39
    @19
    @40
    va
    @16
    cP
    dfss3
    vb
    @15
    cP
    dfss3
    orbi12i
    sylbb2
    syl
    sylbir
    expcom
    syl6
    ralrimdvva
    ex
    adantrd
    imdistand
    @2
    @3
    @12
    df-3an
    @2
    @3
    @22
    df-3an
    3imtr4g
    va
    vb
    cP
    cR
    cG
    cH
    cX
    vr
    vs
    ispridl2.1
    ispridl2.2
    ispridl2.3
    ispridl
    sylibrd
    imp
end
