include "wcel.mm"
include "ccom.mm"
include "cid.mm"
include "cres.mm"
include "wf.mm"
include "wfn.mm"
include "cdif.mm"
include "cdm.mm"
include "cfv.mm"
include "cvv.mm"
include "wss.mm"
include "c2o.mm"
include "cen.mm"
include "wbr.mm"
include "w3a.mm"
include "wceq.mm"
include "eqid.mm"
include "pmtrfrn.mm"
include "simpld.mm"
include "pmtrf.mm"
include "syl.mm"
include "simprd.mm"
include "feq1d.mm"
include "mpbird.mm"
include "fco.mm"
include "anidms.mm"
include "ffn.mm"
include "3syl.mm"
include "fnresi.mm"
include "a1i.mm"
include "cv.mm"
include "wa.mm"
include "csn.mm"
include "cuni.mm"
include "cif.mm"
include "pmtrffv.mm"
include "iftrue.mm"
include "sylan9eq.mm"
include "fveq2d.mm"
include "simpll.mm"
include "simp2d.mm"
include "ad2antrr.mm"
include "c1o.mm"
include "com.mm"
include "csuc.mm"
include "1onn.mm"
include "simp3d.mm"
include "df-2o.mm"
include "syl6breq.mm"
include "simpr.mm"
include "dif1en.mm"
include "syl3anc.mm"
include "en1uniel.mm"
include "eldifad.mm"
include "sseldd.mm"
include "syl2anc.mm"
include "adantr.mm"
include "en2other2.mm"
include "ancoms.mm"
include "sylan.mm"
include "eqtrd.mm"
include "wn.mm"
include "wne.mm"
include "wb.mm"
include "fnelnfp.mm"
include "necon2bbid.mm"
include "biimpar.mm"
include "fveq2.mm"
include "id.mm"
include "pm2.61dan.mm"
include "fvco2.mm"
include "fvresi.mm"
include "adantl.mm"
include "3eqtr4d.mm"
include "eqfnfvd.mm"

theorem pmtrfinv
  let cD: class D
  let cR: class R
  let cT: class T
  let cF: class F
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cP: class P
  let cV: class V
  assume pmtrrn.t: |- T = ( pmTrsp ` D )
  assume pmtrrn.r: |- R = ran T


  assert |- ( F e. R -> ( F o. F ) = ( _I |` D ) )

  proof
    cF
    cR
    wcel
    #
    vx
    cD
    cF
    cF
    ccom
    #
    cid
    cD
    cres
    #
    @0
    cD
    cD
    cF
    wf
    #
    cD
    cD
    @1
    wf
    #
    @1
    cD
    wfn
    @0
    @3
    cD
    cD
    cF
    cid
    cdif
    cdm
    #
    cT
    cfv
    #
    wf
    #
    @0
    cD
    cvv
    wcel
    #
    @5
    cD
    wss
    #
    @5
    c2o
    cen
    wbr
    #
    w3a
    #
    @7
    @0
    @11
    cF
    @6
    wceq
    #
    cD
    @5
    cR
    cT
    cF
    pmtrrn.t
    pmtrrn.r
    @5
    eqid
    #
    pmtrfrn
    #
    simpld
    #
    cD
    @5
    cT
    cvv
    pmtrrn.t
    pmtrf
    syl
    @0
    cD
    cD
    cF
    @6
    @0
    @11
    @12
    @14
    simprd
    feq1d
    mpbird
    #
    @3
    @4
    cD
    cD
    cD
    cF
    cF
    fco
    anidms
    cD
    cD
    @1
    ffn
    3syl
    @2
    cD
    wfn
    @0
    cD
    fnresi
    a1i
    @0
    vx
    cv
    #
    cD
    wcel
    #
    wa
    #
    @17
    cF
    cfv
    #
    cF
    cfv
    #
    @17
    @17
    @1
    cfv
    #
    @17
    @2
    cfv
    #
    @19
    @17
    @5
    wcel
    #
    @21
    @17
    wceq
    #
    @19
    @24
    wa
    #
    @21
    @5
    @17
    csn
    #
    cdif
    #
    cuni
    #
    cF
    cfv
    #
    @17
    @26
    @20
    @29
    cF
    @19
    @24
    @20
    @24
    @29
    @17
    cif
    @29
    cD
    @5
    cR
    cT
    cF
    @17
    pmtrrn.t
    pmtrrn.r
    @13
    pmtrffv
    @24
    @29
    @17
    iftrue
    sylan9eq
    fveq2d
    @26
    @30
    @29
    @5
    wcel
    #
    @5
    @29
    csn
    cdif
    cuni
    #
    @29
    cif
    #
    @17
    @26
    @0
    @29
    cD
    wcel
    @30
    @33
    wceq
    @0
    @18
    @24
    simpll
    @26
    @5
    cD
    @29
    @0
    @9
    @18
    @24
    @0
    @8
    @9
    @10
    @15
    simp2d
    ad2antrr
    @26
    @29
    @5
    @27
    @26
    @28
    c1o
    cen
    wbr
    #
    @29
    @28
    wcel
    @26
    c1o
    com
    wcel
    #
    @5
    c1o
    csuc
    #
    cen
    wbr
    #
    @24
    @34
    @35
    @26
    1onn
    a1i
    @0
    @37
    @18
    @24
    @0
    @5
    c2o
    @36
    cen
    @0
    @8
    @9
    @10
    @15
    simp3d
    #
    df-2o
    syl6breq
    ad2antrr
    @19
    @24
    simpr
    @5
    c1o
    @17
    dif1en
    syl3anc
    @28
    en1uniel
    syl
    eldifad
    #
    sseldd
    cD
    @5
    cR
    cT
    cF
    @29
    pmtrrn.t
    pmtrrn.r
    @13
    pmtrffv
    syl2anc
    @26
    @33
    @32
    @17
    @26
    @31
    @33
    @32
    wceq
    @39
    @31
    @32
    @29
    iftrue
    syl
    @19
    @10
    @24
    @32
    @17
    wceq
    #
    @0
    @10
    @18
    @38
    adantr
    @24
    @10
    @40
    @5
    @17
    en2other2
    ancoms
    sylan
    eqtrd
    eqtrd
    eqtrd
    @19
    @24
    wn
    #
    wa
    @20
    @17
    wceq
    #
    @25
    @19
    @42
    @41
    @19
    @24
    @20
    @17
    @0
    cF
    cD
    wfn
    #
    @18
    @24
    @20
    @17
    wne
    wb
    @0
    @3
    @43
    @16
    cD
    cD
    cF
    ffn
    syl
    #
    cD
    cF
    @17
    fnelnfp
    sylan
    necon2bbid
    biimpar
    @42
    @21
    @20
    @17
    @20
    @17
    cF
    fveq2
    @42
    id
    eqtrd
    syl
    pm2.61dan
    @0
    @43
    @18
    @22
    @21
    wceq
    @44
    cD
    cF
    cF
    @17
    fvco2
    sylan
    @18
    @23
    @17
    wceq
    @0
    cD
    @17
    fvresi
    adantl
    3eqtr4d
    eqfnfvd
end
