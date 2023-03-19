include "cupgr.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cdif.mm"
include "cpr.mm"
include "w3a.mm"
include "cnbgr.mm"
include "co.mm"
include "wnel.mm"
include "wne.mm"
include "wb.mm"
include "simp1l.mm"
include "eldifi.mm"
include "3ad2ant2.mm"
include "eldifsn.mm"
include "anim1i.mm"
include "sylbi.mm"
include "difpr.mm"
include "eleq2s.mm"
include "3ad2ant3.mm"
include "nbupgrel.mm"
include "syl21anc.mm"
include "biimpa.mm"
include "wn.mm"
include "eleq2i.mm"
include "anbi1i.mm"
include "3bitri.mm"
include "simpr.mm"
include "necomd.mm"
include "adantr.mm"
include "nelprd.mm"
include "df-nel.mm"
include "sylibr.mm"
include "cv.mm"
include "neleq2.mm"
include "elrab2.mm"
include "sylanbrc.mm"
include "upgrres1.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "sylbb.mm"
include "jca31.mm"
include "cvtx.mm"
include "cfv.mm"
include "upgrres1lem2.mm"
include "eqcomi.mm"
include "cedg.mm"
include "ciedg.mm"
include "crn.mm"
include "cid.mm"
include "cres.mm"
include "edgval.mm"
include "upgrres1lem3.mm"
include "rneqi.mm"
include "rnresi.mm"
include "3eqtrri.mm"
include "syl.mm"
include "mpbird.mm"
include "ex.mm"

theorem nbupgrres
  let cS: class S
  let ve: setvar e
  let cE: class E
  let cF: class F
  let cG: class G
  let cK: class K
  let cM: class M
  let cN: class N
  let cV: class V
  assume nbupgrres.v: |- V = ( Vtx ` G )
  assume nbupgrres.e: |- E = ( Edg ` G )
  assume nbupgrres.f: |- F = { e e. E | N e/ e }
  assume nbupgrres.s: |- S = <. ( V \ { N } ) , ( _I |` F ) >.

  disjoint E e
  disjoint G e
  disjoint K e
  disjoint N e
  disjoint M e
  disjoint V e
  assert |- ( ( ( G e. UPGraph /\ N e. V ) /\ K e. ( V \ { N } ) /\ M e. ( V \ { N , K } ) ) -> ( M e. ( G NeighbVtx K ) -> M e. ( S NeighbVtx K ) ) )

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
    cK
    cV
    cN
    csn
    #
    cdif
    #
    wcel
    #
    cM
    cV
    cN
    cK
    cpr
    cdif
    #
    wcel
    #
    w3a
    #
    cM
    cG
    cK
    cnbgr
    co
    wcel
    #
    cM
    cS
    cK
    cnbgr
    co
    wcel
    #
    @8
    @9
    wa
    #
    @10
    cM
    cK
    cpr
    #
    cF
    wcel
    #
    @11
    @12
    cE
    wcel
    #
    cN
    @12
    wnel
    #
    @13
    @8
    @9
    @14
    @8
    @0
    cK
    cV
    wcel
    #
    cM
    cV
    wcel
    #
    cM
    cK
    wne
    #
    wa
    #
    @9
    @14
    wb
    @0
    @1
    @5
    @7
    simp1l
    @5
    @2
    @16
    @7
    cK
    cV
    @3
    eldifi
    3ad2ant2
    @7
    @2
    @19
    @5
    @19
    cM
    @4
    cK
    csn
    cdif
    #
    @6
    cM
    @20
    wcel
    #
    cM
    @4
    wcel
    #
    @18
    wa
    #
    @19
    cM
    @4
    cK
    eldifsn
    #
    @22
    @17
    @18
    cM
    cV
    @3
    eldifi
    anim1i
    sylbi
    cV
    cN
    cK
    difpr
    #
    eleq2s
    3ad2ant3
    cE
    cG
    cK
    cM
    cV
    nbupgrres.v
    nbupgrres.e
    nbupgrel
    syl21anc
    biimpa
    @8
    @15
    @9
    @8
    cN
    @12
    wcel
    wn
    @15
    @8
    cN
    cM
    cK
    @7
    @2
    cN
    cM
    wne
    #
    @5
    @7
    @17
    cM
    cN
    wne
    #
    wa
    #
    @18
    wa
    #
    @26
    @7
    @21
    @23
    @29
    @6
    @20
    cM
    @25
    eleq2i
    #
    @24
    @22
    @28
    @18
    cM
    cV
    cN
    eldifsn
    anbi1i
    3bitri
    @28
    @26
    @18
    @28
    cM
    cN
    @17
    @27
    simpr
    necomd
    adantr
    sylbi
    3ad2ant3
    @5
    @2
    cN
    cK
    wne
    #
    @7
    @5
    @16
    cK
    cN
    wne
    #
    wa
    #
    @31
    cK
    cV
    cN
    eldifsn
    @33
    cK
    cN
    @16
    @32
    simpr
    necomd
    sylbi
    3ad2ant2
    nelprd
    cN
    @12
    df-nel
    sylibr
    adantr
    cN
    ve
    cv
    #
    wnel
    @15
    ve
    @12
    cE
    cF
    @34
    @12
    cN
    neleq2
    nbupgrres.f
    elrab2
    sylanbrc
    @11
    cS
    cupgr
    wcel
    #
    @5
    wa
    @23
    wa
    #
    @10
    @13
    wb
    @8
    @36
    @9
    @8
    @35
    @5
    @23
    @2
    @5
    @35
    @7
    cS
    ve
    cE
    cF
    cG
    cN
    cV
    nbupgrres.v
    nbupgrres.e
    nbupgrres.f
    nbupgrres.s
    upgrres1
    3ad2ant1
    @2
    @5
    @7
    simp2
    @7
    @2
    @23
    @5
    @7
    @21
    @23
    @30
    @24
    sylbb
    3ad2ant3
    jca31
    adantr
    cF
    cS
    cK
    cM
    @4
    cS
    cvtx
    cfv
    @4
    cS
    ve
    cE
    cF
    cG
    cN
    cV
    nbupgrres.v
    nbupgrres.e
    nbupgrres.f
    nbupgrres.s
    upgrres1lem2
    eqcomi
    cS
    cedg
    cfv
    cS
    ciedg
    cfv
    #
    crn
    cid
    cF
    cres
    #
    crn
    cF
    cS
    edgval
    @37
    @38
    cS
    ve
    cE
    cF
    cG
    cN
    cV
    nbupgrres.v
    nbupgrres.e
    nbupgrres.f
    nbupgrres.s
    upgrres1lem3
    rneqi
    cF
    rnresi
    3eqtrri
    nbupgrel
    syl
    mpbird
    ex
end
