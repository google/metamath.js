include "cconngr.mm"
include "wcel.mm"
include "c1.mm"
include "chash.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cv.mm"
include "wne.mm"
include "wrex.mm"
include "crn.mm"
include "cvv.mm"
include "cvtx.mm"
include "fvex.mm"
include "eqeltri.mm"
include "simp3.mm"
include "simp2.mm"
include "hashgt12el2.mm"
include "mp3an2i.mm"
include "wa.mm"
include "wi.mm"
include "cpthson.mm"
include "co.mm"
include "wex.mm"
include "wral.mm"
include "isconngr.mm"
include "wceq.mm"
include "oveq1.mm"
include "breqd.mm"
include "2exbidv.mm"
include "weq.mm"
include "oveq2.mm"
include "rspc2v.mm"
include "ad2ant2r.mm"
include "cwlkson.mm"
include "cc0.mm"
include "ctrlson.mm"
include "pthontrlon.mm"
include "trlsonwlkon.mm"
include "simpl.mm"
include "simprr.mm"
include "wlkon2n0.mm"
include "sylan2.mm"
include "jca.mm"
include "ex.mm"
include "3syl.mm"
include "wlkonl1iedg.mm"
include "syl6com.mm"
include "exlimdvv.mm"
include "syldc.mm"
include "syl6bi.mm"
include "pm2.43i.mm"
include "expd.mm"
include "3impib.mm"
include "rexlimdv.mm"
include "mpd.mm"

theorem conngrv2edg
  let ve: setvar e
  let cG: class G
  let cI: class I
  let cN: class N
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vp: setvar p
  let vv: setvar v
  assume conngrv2edg.v: |- V = ( Vtx ` G )
  assume conngrv2edg.i: |- I = ( iEdg ` G )

  disjoint G e
  disjoint I e
  disjoint N e
  disjoint G a
  disjoint G b
  disjoint a b
  disjoint G f
  disjoint G p
  disjoint G v
  disjoint e f
  disjoint e p
  disjoint e v
  disjoint f p
  disjoint f v
  disjoint p v
  disjoint a f
  disjoint a p
  disjoint b f
  disjoint b p
  disjoint I f
  disjoint I p
  disjoint I v
  disjoint N a
  disjoint N b
  disjoint N v
  disjoint a v
  disjoint b v
  disjoint N f
  disjoint N p
  disjoint V a
  disjoint V b
  disjoint V v
  disjoint V f
  disjoint V p
  assert |- ( ( G e. ConnGraph /\ N e. V /\ 1 < ( # ` V ) ) -> E. e e. ran I N e. e )

  proof
    cG
    cconngr
    wcel
    #
    cN
    cV
    wcel
    #
    c1
    cV
    chash
    cfv
    clt
    wbr
    #
    w3a
    #
    cN
    vv
    cv
    #
    wne
    #
    vv
    cV
    wrex
    #
    cN
    ve
    cv
    wcel
    ve
    cI
    crn
    wrex
    #
    cV
    cvv
    wcel
    @3
    @2
    @1
    @6
    cV
    cG
    cvtx
    cfv
    cvv
    conngrv2edg.v
    cG
    cvtx
    fvex
    eqeltri
    @0
    @1
    @2
    simp3
    @0
    @1
    @2
    simp2
    cN
    cV
    cvv
    vv
    hashgt12el2
    mp3an2i
    @3
    @5
    @7
    vv
    cV
    @3
    @4
    cV
    wcel
    #
    @5
    @7
    @0
    @1
    @2
    @8
    @5
    wa
    #
    @7
    wi
    @0
    @1
    @2
    wa
    #
    @9
    @7
    @0
    @10
    @9
    wa
    #
    @7
    wi
    #
    @0
    @0
    vf
    cv
    #
    vp
    cv
    #
    va
    cv
    #
    vb
    cv
    #
    cG
    cpthson
    cfv
    #
    co
    #
    wbr
    #
    vp
    wex
    vf
    wex
    #
    vb
    cV
    wral
    va
    cV
    wral
    #
    @12
    vf
    va
    vb
    cG
    cV
    cconngr
    vp
    conngrv2edg.v
    isconngr
    @11
    @21
    @13
    @14
    cN
    @4
    @17
    co
    #
    wbr
    #
    vp
    wex
    vf
    wex
    #
    @7
    @1
    @8
    @21
    @24
    wi
    @2
    @5
    @20
    @24
    @13
    @14
    cN
    @16
    @17
    co
    #
    wbr
    #
    vp
    wex
    vf
    wex
    va
    vb
    cN
    @4
    cV
    cV
    @15
    cN
    wceq
    #
    @19
    @26
    vf
    vp
    @27
    @18
    @25
    @13
    @14
    @15
    cN
    @16
    @17
    oveq1
    breqd
    2exbidv
    vb
    vv
    weq
    #
    @26
    @23
    vf
    vp
    @28
    @25
    @22
    @13
    @14
    @16
    @4
    cN
    @17
    oveq2
    breqd
    2exbidv
    rspc2v
    ad2ant2r
    @11
    @23
    @7
    vf
    vp
    @23
    @11
    @13
    @14
    cN
    @4
    cG
    cwlkson
    cfv
    co
    wbr
    #
    @13
    chash
    cfv
    cc0
    wne
    #
    wa
    #
    @7
    @23
    @13
    @14
    cN
    @4
    cG
    ctrlson
    cfv
    co
    wbr
    @29
    @11
    @31
    wi
    cN
    @4
    @14
    @13
    cG
    pthontrlon
    cN
    @4
    @14
    @13
    cG
    trlsonwlkon
    @29
    @11
    @31
    @29
    @11
    wa
    @29
    @30
    @29
    @11
    simpl
    @11
    @29
    @5
    @30
    @10
    @8
    @5
    simprr
    cN
    @4
    @14
    @13
    cG
    wlkon2n0
    sylan2
    jca
    ex
    3syl
    cN
    @4
    @14
    ve
    @13
    cG
    cI
    conngrv2edg.i
    wlkonl1iedg
    syl6com
    exlimdvv
    syldc
    syl6bi
    pm2.43i
    expd
    3impib
    expd
    rexlimdv
    mpd
end
