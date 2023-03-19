include "cusgr.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cpr.mm"
include "wceq.mm"
include "weu.mm"
include "wreu.mm"
include "cvtx.mm"
include "cfv.mm"
include "cedg.mm"
include "simpl.mm"
include "adantr.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "ad2antrl.mm"
include "simprr.mm"
include "usgredg2vtxeu.mm"
include "syl3anc.mm"
include "df-reu.mm"
include "wi.mm"
include "prcom.mm"
include "eqeq2i.mm"
include "eleq1d.mm"
include "biimpcd.mm"
include "adantld.mm"
include "imp.mm"
include "jca.mm"
include "eqid.mm"
include "usgrpredgv.mm"
include "simpld.mm"
include "syl2an.mm"
include "impbida.mm"
include "eubidv.mm"
include "biimpd.mm"
include "syl5bi.mm"
include "mpd.mm"
include "wb.mm"
include "cnbgr.mm"
include "co.mm"
include "nbusgreledg.mm"
include "syl5bb.mm"
include "anbi1d.mm"
include "ad2antrr.mm"
include "mpbird.mm"
include "sylibr.mm"

theorem edgnbusgreu
  let cC: class C
  let vn: setvar n
  let cE: class E
  let cG: class G
  let cM: class M
  let cN: class N
  let cV: class V
  assume edgnbusgreu.v: |- V = ( Vtx ` G )
  assume edgnbusgreu.e: |- E = ( Edg ` G )
  assume edgnbusgreu.n: |- N = ( G NeighbVtx M )

  disjoint C n
  disjoint E n
  disjoint G n
  disjoint M n
  disjoint V n
  assert |- ( ( ( G e. USGraph /\ M e. V ) /\ ( C e. E /\ M e. C ) ) -> E! n e. N C = { M , n } )

  proof
    cG
    cusgr
    wcel
    #
    cM
    cV
    wcel
    #
    wa
    #
    cC
    cE
    wcel
    #
    cM
    cC
    wcel
    #
    wa
    #
    wa
    #
    vn
    cv
    #
    cN
    wcel
    #
    cC
    cM
    @7
    cpr
    #
    wceq
    #
    wa
    #
    vn
    weu
    #
    @10
    vn
    cN
    wreu
    @6
    @12
    @7
    cM
    cpr
    #
    cE
    wcel
    #
    @10
    wa
    #
    vn
    weu
    #
    @6
    @10
    vn
    cG
    cvtx
    cfv
    #
    wreu
    #
    @16
    @6
    @0
    cC
    cG
    cedg
    cfv
    #
    wcel
    #
    @4
    @18
    @2
    @0
    @5
    @0
    @1
    simpl
    adantr
    #
    @3
    @20
    @2
    @4
    @3
    @20
    cE
    @19
    cC
    edgnbusgreu.e
    eleq2i
    biimpi
    ad2antrl
    @2
    @3
    @4
    simprr
    vn
    cC
    cG
    cM
    usgredg2vtxeu
    syl3anc
    @18
    @7
    @17
    wcel
    #
    @10
    wa
    #
    vn
    weu
    #
    @6
    @16
    @10
    vn
    @17
    df-reu
    @6
    @24
    @16
    @6
    @23
    @15
    vn
    @6
    @23
    @15
    @6
    @23
    wa
    @14
    @10
    @6
    @23
    @14
    @6
    @10
    @14
    @22
    @3
    @10
    @14
    wi
    @2
    @4
    @10
    @3
    @14
    @10
    cC
    @13
    cE
    @10
    cC
    @13
    wceq
    @9
    @13
    cC
    cM
    @7
    prcom
    eqeq2i
    biimpi
    eleq1d
    biimpcd
    ad2antrl
    adantld
    imp
    @6
    @22
    @10
    simprr
    jca
    @6
    @15
    wa
    @22
    @10
    @6
    @0
    @14
    @22
    @15
    @21
    @14
    @10
    simpl
    @0
    @14
    wa
    @22
    cM
    @17
    wcel
    cE
    cG
    @7
    cM
    @17
    edgnbusgreu.e
    @17
    eqid
    usgrpredgv
    simpld
    syl2an
    @6
    @14
    @10
    simprr
    jca
    impbida
    eubidv
    biimpd
    syl5bi
    mpd
    @6
    @11
    @15
    vn
    @0
    @11
    @15
    wb
    @1
    @5
    @0
    @8
    @14
    @10
    @8
    @7
    cG
    cM
    cnbgr
    co
    #
    wcel
    @0
    @14
    cN
    @25
    @7
    edgnbusgreu.n
    eleq2i
    cE
    cG
    cM
    @7
    edgnbusgreu.e
    nbusgreledg
    syl5bb
    anbi1d
    ad2antrr
    eubidv
    mpbird
    @10
    vn
    cN
    df-reu
    sylibr
end
