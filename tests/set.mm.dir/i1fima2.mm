include "citg1.mm"
include "cdm.mm"
include "wcel.mm"
include "cc0.mm"
include "wn.mm"
include "wa.mm"
include "ccnv.mm"
include "cima.mm"
include "cvol.mm"
include "cfv.mm"
include "covol.mm"
include "cr.mm"
include "wceq.mm"
include "i1fima.mm"
include "adantr.mm"
include "mblvol.mm"
include "syl.mm"
include "csn.mm"
include "cdif.mm"
include "wss.mm"
include "crn.mm"
include "cin.mm"
include "wf.mm"
include "wfun.mm"
include "i1ff.mm"
include "ffun.mm"
include "inpreima.mm"
include "3syl.mm"
include "cnvimass.mm"
include "cnvimarndm.mm"
include "sseqtr4i.mm"
include "df-ss.mm"
include "mpbi.mm"
include "syl6req.mm"
include "c0.mm"
include "inss1.mm"
include "sseli.mm"
include "con3i.mm"
include "adantl.mm"
include "disjsn.mm"
include "sylibr.mm"
include "wb.mm"
include "inss2.mm"
include "frn.mm"
include "syl5ss.mm"
include "reldisj.mm"
include "mpbid.mm"
include "imass2.mm"
include "eqsstrd.mm"
include "mblss.mm"
include "cfn.mm"
include "cmbf.mm"
include "w3a.mm"
include "isi1f.mm"
include "simprbi.mm"
include "simp3d.mm"
include "eqeltrrd.mm"
include "ovolsscl.mm"
include "syl3anc.mm"
include "eqeltrd.mm"

theorem i1fima2
  let cA: class A
  let cF: class F
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( F e. dom S.1 /\ -. 0 e. A ) -> ( vol ` ( `' F " A ) ) e. RR )

  proof
    cF
    citg1
    cdm
    wcel
    #
    cc0
    cA
    wcel
    #
    wn
    #
    wa
    #
    cF
    ccnv
    #
    cA
    cima
    #
    cvol
    cfv
    #
    @5
    covol
    cfv
    #
    cr
    @3
    @5
    cvol
    cdm
    #
    wcel
    #
    @6
    @7
    wceq
    @0
    @9
    @2
    cA
    cF
    i1fima
    adantr
    @5
    mblvol
    syl
    @3
    @5
    @4
    cr
    cc0
    csn
    #
    cdif
    #
    cima
    #
    wss
    @12
    cr
    wss
    #
    @12
    covol
    cfv
    #
    cr
    wcel
    @7
    cr
    wcel
    @3
    @5
    @4
    cA
    cF
    crn
    #
    cin
    #
    cima
    #
    @12
    @3
    @17
    @5
    @4
    @15
    cima
    #
    cin
    #
    @5
    @3
    cr
    cr
    cF
    wf
    #
    cF
    wfun
    @17
    @19
    wceq
    @0
    @20
    @2
    cF
    i1ff
    #
    adantr
    cr
    cr
    cF
    ffun
    cA
    @15
    cF
    inpreima
    3syl
    @5
    @18
    wss
    @19
    @5
    wceq
    @5
    cF
    cdm
    @18
    cF
    cA
    cnvimass
    cF
    cnvimarndm
    sseqtr4i
    @5
    @18
    df-ss
    mpbi
    syl6req
    @3
    @16
    @11
    wss
    #
    @17
    @12
    wss
    @3
    @16
    @10
    cin
    c0
    wceq
    #
    @22
    @3
    cc0
    @16
    wcel
    #
    wn
    #
    @23
    @2
    @25
    @0
    @24
    @1
    @16
    cA
    cc0
    cA
    @15
    inss1
    sseli
    con3i
    adantl
    @16
    cc0
    disjsn
    sylibr
    @3
    @16
    cr
    wss
    #
    @23
    @22
    wb
    @0
    @26
    @2
    @0
    @16
    @15
    cr
    cA
    @15
    inss2
    @0
    @20
    @15
    cr
    wss
    @21
    cr
    cr
    cF
    frn
    syl
    syl5ss
    adantr
    @16
    @10
    cr
    reldisj
    syl
    mpbid
    @16
    @11
    @4
    imass2
    syl
    eqsstrd
    @3
    @12
    @8
    wcel
    #
    @13
    @0
    @27
    @2
    @11
    cF
    i1fima
    adantr
    #
    @12
    mblss
    syl
    @3
    @12
    cvol
    cfv
    #
    @14
    cr
    @3
    @27
    @29
    @14
    wceq
    @28
    @12
    mblvol
    syl
    @0
    @29
    cr
    wcel
    #
    @2
    @0
    @20
    @15
    cfn
    wcel
    #
    @30
    @0
    cF
    cmbf
    wcel
    @20
    @31
    @30
    w3a
    cF
    isi1f
    simprbi
    simp3d
    adantr
    eqeltrrd
    @5
    @12
    ovolsscl
    syl3anc
    eqeltrd
end
