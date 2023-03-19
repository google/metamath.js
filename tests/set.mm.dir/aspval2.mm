include "casa.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "csubrg.mm"
include "cfv.mm"
include "clss.mm"
include "cin.mm"
include "crab.mm"
include "cint.mm"
include "crn.mm"
include "cun.mm"
include "cab.mm"
include "wceq.mm"
include "elin.mm"
include "anbi1i.mm"
include "anass.mm"
include "bitri.mm"
include "eqid.mm"
include "issubassa2.mm"
include "anbi1d.mm"
include "unss.mm"
include "syl6bb.mm"
include "pm5.32da.mm"
include "syl5bb.mm"
include "abbidv.mm"
include "adantr.mm"
include "df-rab.mm"
include "3eqtr4g.mm"
include "inteqd.mm"
include "aspval.mm"
include "cmre.mm"
include "crg.mm"
include "assaring.mm"
include "subrgmre.mm"
include "syl.mm"
include "csca.mm"
include "cbs.mm"
include "wf.mm"
include "assalmod.mm"
include "asclf.mm"
include "frn.mm"
include "simpr.mm"
include "unssd.mm"
include "mrcval.mm"
include "syl2anc.mm"
include "3eqtr4d.mm"

theorem aspval2
  let cA: class A
  let cC: class C
  let cR: class R
  let cS: class S
  let cV: class V
  let cW: class W
  let vx: setvar x
  assume aspval2.a: |- A = ( AlgSpan ` W )
  assume aspval2.c: |- C = ( algSc ` W )
  assume aspval2.r: |- R = ( mrCls ` ( SubRing ` W ) )
  assume aspval2.v: |- V = ( Base ` W )


  assert |- ( ( W e. AssAlg /\ S C_ V ) -> ( A ` S ) = ( R ` ( ran C u. S ) ) )

  proof
    cW
    casa
    wcel
    #
    cS
    cV
    wss
    #
    wa
    #
    cS
    vx
    cv
    #
    wss
    #
    vx
    cW
    csubrg
    cfv
    #
    cW
    clss
    cfv
    #
    cin
    #
    crab
    #
    cint
    cC
    crn
    #
    cS
    cun
    #
    @3
    wss
    #
    vx
    @5
    crab
    #
    cint
    #
    cS
    cA
    cfv
    @10
    cR
    cfv
    #
    @2
    @8
    @12
    @2
    @3
    @7
    wcel
    #
    @4
    wa
    #
    vx
    cab
    #
    @3
    @5
    wcel
    #
    @11
    wa
    #
    vx
    cab
    #
    @8
    @12
    @0
    @17
    @20
    wceq
    @1
    @0
    @16
    @19
    vx
    @16
    @18
    @3
    @6
    wcel
    #
    @4
    wa
    #
    wa
    #
    @0
    @19
    @16
    @18
    @21
    wa
    #
    @4
    wa
    @23
    @15
    @24
    @4
    @3
    @5
    @6
    elin
    anbi1i
    @18
    @21
    @4
    anass
    bitri
    @0
    @18
    @22
    @11
    @0
    @18
    wa
    #
    @22
    @9
    @3
    wss
    #
    @4
    wa
    @11
    @25
    @21
    @26
    @4
    cC
    @3
    @6
    cW
    aspval2.c
    @6
    eqid
    #
    issubassa2
    anbi1d
    @9
    cS
    @3
    unss
    syl6bb
    pm5.32da
    syl5bb
    abbidv
    adantr
    @4
    vx
    @7
    df-rab
    @11
    vx
    @5
    df-rab
    3eqtr4g
    inteqd
    vx
    cA
    cS
    @6
    cV
    cW
    aspval2.a
    aspval2.v
    @27
    aspval
    @2
    @5
    cV
    cmre
    cfv
    wcel
    #
    @10
    cV
    wss
    @14
    @13
    wceq
    @0
    @28
    @1
    @0
    cW
    crg
    wcel
    @28
    cW
    assaring
    #
    cV
    cW
    aspval2.v
    subrgmre
    syl
    adantr
    @2
    @9
    cS
    cV
    @0
    @9
    cV
    wss
    #
    @1
    @0
    cW
    csca
    cfv
    #
    cbs
    cfv
    #
    cV
    cC
    wf
    @30
    @0
    cC
    cV
    @31
    @32
    cW
    aspval2.c
    @31
    eqid
    @29
    cW
    assalmod
    @32
    eqid
    aspval2.v
    asclf
    @32
    cV
    cC
    frn
    syl
    adantr
    @0
    @1
    simpr
    unssd
    @5
    @10
    cR
    cV
    vx
    aspval2.r
    mrcval
    syl2anc
    3eqtr4d
end
