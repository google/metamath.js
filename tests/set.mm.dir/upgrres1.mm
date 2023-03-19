include "cupgr.mm"
include "wcel.mm"
include "wa.mm"
include "cid.mm"
include "cres.mm"
include "cdm.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "cle.mm"
include "wbr.mm"
include "csn.mm"
include "cdif.mm"
include "cpw.mm"
include "c0.mm"
include "crab.mm"
include "wf.mm"
include "wf1o.mm"
include "f1oi.mm"
include "f1of.mm"
include "mp1i.mm"
include "ffdmd.mm"
include "wnel.mm"
include "wi.mm"
include "wral.mm"
include "wss.mm"
include "simpr.mm"
include "adantr.mm"
include "cedg.mm"
include "eleq2i.mm"
include "cvtx.mm"
include "wne.mm"
include "w3a.mm"
include "edgupgr.mm"
include "elpwi.mm"
include "syl6sseqr.mm"
include "3ad2ant1.mm"
include "syl.mm"
include "sylan2b.mm"
include "ad4ant13.mm"
include "elpwdifsn.mm"
include "syl3anc.mm"
include "wn.mm"
include "simpl.mm"
include "biimpi.mm"
include "simp2d.mm"
include "syl2an.mm"
include "nelsn.mm"
include "eldifd.mm"
include "ex.mm"
include "ralrimiva.mm"
include "rabss.mm"
include "sylibr.mm"
include "syl5eqss.mm"
include "elrabi.mm"
include "ciedg.mm"
include "crn.mm"
include "edgval.mm"
include "eqtri.mm"
include "eqid.mm"
include "upgrf.mm"
include "frn.mm"
include "sseld.mm"
include "syl5bi.mm"
include "wceq.mm"
include "fveq2.mm"
include "breq1d.mm"
include "elrab.mm"
include "simprbi.mm"
include "syl6.mm"
include "syl5com.mm"
include "eleq2s.mm"
include "impcom.mm"
include "ssrabdv.mm"
include "fssd.mm"
include "cvv.mm"
include "wb.mm"
include "cop.mm"
include "opex.mm"
include "eqeltri.mm"
include "upgrres1lem2.mm"
include "eqcomi.mm"
include "upgrres1lem3.mm"
include "isupgr.mm"
include "mpbird.mm"

theorem upgrres1
  let cS: class S
  let ve: setvar e
  let cE: class E
  let cF: class F
  let cG: class G
  let cN: class N
  let cV: class V
  let vp: setvar p
  let vx: setvar x
  assume upgrres1.v: |- V = ( Vtx ` G )
  assume upgrres1.e: |- E = ( Edg ` G )
  assume upgrres1.f: |- F = { e e. E | N e/ e }
  assume upgrres1.s: |- S = <. ( V \ { N } ) , ( _I |` F ) >.

  disjoint E e
  disjoint G e
  disjoint N e
  disjoint V e
  disjoint F p
  disjoint G p
  disjoint N p
  disjoint V p
  disjoint e p
  disjoint G x
  disjoint p x
  disjoint S p
  disjoint V x
  assert |- ( ( G e. UPGraph /\ N e. V ) -> S e. UPGraph )

  proof
    cG
    cupgr
    wcel
    #
    cN
    cV
    wcel
    #
    wa
    #
    cS
    cupgr
    wcel
    #
    cid
    cF
    cres
    #
    cdm
    #
    vp
    cv
    #
    chash
    cfv
    #
    c2
    cle
    wbr
    #
    vp
    cV
    cN
    csn
    cdif
    #
    cpw
    #
    c0
    csn
    #
    cdif
    #
    crab
    #
    @4
    wf
    #
    @2
    @5
    cF
    @13
    @4
    @2
    cF
    cF
    @4
    cF
    cF
    @4
    wf1o
    cF
    cF
    @4
    wf
    @2
    cF
    f1oi
    cF
    cF
    @4
    f1of
    mp1i
    ffdmd
    @2
    @8
    vp
    @12
    cF
    @2
    cF
    cN
    ve
    cv
    #
    wnel
    #
    ve
    cE
    crab
    #
    @12
    upgrres1.f
    @2
    @16
    @15
    @12
    wcel
    #
    wi
    #
    ve
    cE
    wral
    @17
    @12
    wss
    @2
    @19
    ve
    cE
    @2
    @15
    cE
    wcel
    #
    wa
    #
    @16
    @18
    @21
    @16
    wa
    #
    @15
    @10
    @11
    @22
    @20
    @15
    cV
    wss
    #
    @16
    @15
    @10
    wcel
    @21
    @20
    @16
    @2
    @20
    simpr
    adantr
    @0
    @20
    @23
    @1
    @16
    @20
    @0
    @15
    cG
    cedg
    cfv
    #
    wcel
    #
    @23
    cE
    @24
    @15
    upgrres1.e
    eleq2i
    #
    @0
    @25
    wa
    #
    @15
    cG
    cvtx
    cfv
    #
    cpw
    wcel
    #
    @15
    c0
    wne
    #
    @15
    chash
    cfv
    c2
    cle
    wbr
    #
    w3a
    @23
    @15
    cG
    edgupgr
    #
    @29
    @30
    @23
    @31
    @29
    @15
    @28
    cV
    @15
    @28
    elpwi
    upgrres1.v
    syl6sseqr
    3ad2ant1
    syl
    sylan2b
    ad4ant13
    @21
    @16
    simpr
    cN
    @15
    cV
    cE
    elpwdifsn
    syl3anc
    @22
    @30
    @15
    @11
    wcel
    wn
    @21
    @30
    @16
    @2
    @0
    @25
    @30
    @20
    @0
    @1
    simpl
    @20
    @25
    @26
    biimpi
    @27
    @29
    @30
    @31
    @32
    simp2d
    syl2an
    adantr
    @15
    c0
    nelsn
    syl
    eldifd
    ex
    ralrimiva
    @16
    ve
    cE
    @12
    rabss
    sylibr
    syl5eqss
    @6
    cF
    wcel
    @2
    @8
    @2
    @8
    wi
    @6
    @17
    cF
    @6
    @17
    wcel
    @6
    cE
    wcel
    #
    @2
    @8
    @16
    ve
    @6
    cE
    elrabi
    @0
    @33
    @8
    wi
    @1
    @0
    @33
    @6
    vx
    cv
    #
    chash
    cfv
    #
    c2
    cle
    wbr
    #
    vx
    cV
    cpw
    @11
    cdif
    #
    crab
    #
    wcel
    #
    @8
    @33
    @6
    cG
    ciedg
    cfv
    #
    crn
    #
    wcel
    @0
    @39
    cE
    @41
    @6
    cE
    @24
    @41
    upgrres1.e
    cG
    edgval
    eqtri
    eleq2i
    @0
    @41
    @38
    @6
    @0
    @40
    cdm
    #
    @38
    @40
    wf
    @41
    @38
    wss
    vx
    @40
    cG
    cV
    upgrres1.v
    @40
    eqid
    upgrf
    @42
    @38
    @40
    frn
    syl
    sseld
    syl5bi
    @39
    @6
    @37
    wcel
    @8
    @36
    @8
    vx
    @6
    @37
    @34
    @6
    wceq
    @35
    @7
    c2
    cle
    @34
    @6
    chash
    fveq2
    breq1d
    elrab
    simprbi
    syl6
    adantr
    syl5com
    upgrres1.f
    eleq2s
    impcom
    ssrabdv
    fssd
    cS
    cvv
    wcel
    @3
    @14
    wb
    @2
    cS
    @9
    @4
    cop
    cvv
    upgrres1.s
    @9
    @4
    opex
    eqeltri
    vp
    cvv
    @4
    cS
    @9
    cS
    cvtx
    cfv
    @9
    cS
    ve
    cE
    cF
    cG
    cN
    cV
    upgrres1.v
    upgrres1.e
    upgrres1.f
    upgrres1.s
    upgrres1lem2
    eqcomi
    cS
    ciedg
    cfv
    @4
    cS
    ve
    cE
    cF
    cG
    cN
    cV
    upgrres1.v
    upgrres1.e
    upgrres1.f
    upgrres1.s
    upgrres1lem3
    eqcomi
    isupgr
    mp1i
    mpbird
end
