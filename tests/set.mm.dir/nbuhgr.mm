include "wcel.mm"
include "cuhgr.mm"
include "wa.mm"
include "cnbgr.mm"
include "co.mm"
include "cv.mm"
include "cpr.mm"
include "wss.mm"
include "wrex.mm"
include "csn.mm"
include "cdif.mm"
include "crab.mm"
include "wceq.mm"
include "wi.mm"
include "nbgrval.mm"
include "a1d.mm"
include "wn.mm"
include "c0.mm"
include "wnel.mm"
include "df-nel.mm"
include "nbgrnvtx0.mm"
include "sylbir.mm"
include "adantr.mm"
include "wral.mm"
include "cvtx.mm"
include "cfv.mm"
include "cpw.mm"
include "cedg.mm"
include "simpl.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "edguhgr.mm"
include "syl2an.mm"
include "selpw.mm"
include "eqcomi.mm"
include "sseq2i.mm"
include "bitri.mm"
include "sstr.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "prssg.mm"
include "bicomd.mm"
include "mpan2.mm"
include "syl6bi.mm"
include "syl5com.mm"
include "ex.mm"
include "com13.mm"
include "ad3antlr.mm"
include "syl5bi.mm"
include "mpd.mm"
include "rexlimdva.mm"
include "con3rr3.mm"
include "expdimp.mm"
include "ralrimiv.mm"
include "rabeq0.mm"
include "sylibr.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"

theorem nbuhgr
  let ve: setvar e
  let vn: setvar n
  let cE: class E
  let cG: class G
  let cN: class N
  let cV: class V
  let cX: class X
  assume nbuhgr.v: |- V = ( Vtx ` G )
  assume nbuhgr.e: |- E = ( Edg ` G )

  disjoint E e
  disjoint G e
  disjoint G n
  disjoint e n
  disjoint N e
  disjoint N n
  disjoint V e
  disjoint V n
  disjoint X e
  disjoint X n
  assert |- ( ( G e. UHGraph /\ N e. X ) -> ( G NeighbVtx N ) = { n e. ( V \ { N } ) | E. e e. E { N , n } C_ e } )

  proof
    cN
    cV
    wcel
    #
    cG
    cuhgr
    wcel
    #
    cN
    cX
    wcel
    #
    wa
    #
    cG
    cN
    cnbgr
    co
    #
    cN
    vn
    cv
    #
    cpr
    #
    ve
    cv
    #
    wss
    #
    ve
    cE
    wrex
    #
    vn
    cV
    cN
    csn
    cdif
    #
    crab
    #
    wceq
    #
    wi
    @0
    @12
    @3
    ve
    vn
    cE
    cG
    cN
    cV
    nbuhgr.v
    nbuhgr.e
    nbgrval
    a1d
    @0
    wn
    #
    @3
    @12
    @13
    @3
    wa
    #
    @4
    c0
    @11
    @13
    @4
    c0
    wceq
    #
    @3
    @13
    cN
    cV
    wnel
    @15
    cN
    cV
    df-nel
    cG
    cV
    cN
    nbuhgr.v
    nbgrnvtx0
    sylbir
    adantr
    @14
    @9
    wn
    #
    vn
    @10
    wral
    @11
    c0
    wceq
    @14
    @16
    vn
    @10
    @13
    @3
    @5
    @10
    wcel
    #
    @16
    @3
    @17
    wa
    #
    @9
    @0
    @18
    @8
    @0
    ve
    cE
    @18
    @7
    cE
    wcel
    #
    wa
    #
    @7
    cG
    cvtx
    cfv
    #
    cpw
    wcel
    #
    @8
    @0
    wi
    #
    @18
    @1
    @7
    cG
    cedg
    cfv
    #
    wcel
    #
    @22
    @19
    @3
    @1
    @17
    @1
    @2
    simpl
    adantr
    @19
    @25
    cE
    @24
    @7
    nbuhgr.e
    eleq2i
    biimpi
    @7
    cG
    edguhgr
    syl2an
    @22
    @7
    cV
    wss
    #
    @20
    @23
    @22
    @7
    @21
    wss
    @26
    ve
    @21
    selpw
    @21
    cV
    @7
    cV
    @21
    nbuhgr.v
    eqcomi
    sseq2i
    bitri
    @2
    @26
    @23
    wi
    @1
    @17
    @19
    @8
    @26
    @2
    @0
    @8
    @26
    @2
    @0
    wi
    @8
    @26
    wa
    @6
    cV
    wss
    #
    @2
    @0
    @6
    @7
    cV
    sstr
    @2
    @27
    @0
    @5
    cV
    wcel
    #
    wa
    #
    @0
    @2
    @5
    cvv
    wcel
    #
    @27
    @29
    wb
    vn
    vex
    @2
    @30
    wa
    @29
    @27
    cN
    @5
    cV
    cX
    cvv
    prssg
    bicomd
    mpan2
    @0
    @28
    simpl
    syl6bi
    syl5com
    ex
    com13
    ad3antlr
    syl5bi
    mpd
    rexlimdva
    con3rr3
    expdimp
    ralrimiv
    @9
    vn
    @10
    rabeq0
    sylibr
    eqtr4d
    ex
    pm2.61i
end
