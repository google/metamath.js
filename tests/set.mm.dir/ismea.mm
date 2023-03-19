include "cmea.mm"
include "wcel.mm"
include "cdm.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "csalg.mm"
include "wa.mm"
include "c0.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wdisj.mm"
include "cuni.mm"
include "cres.mm"
include "csumge0.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "id.mm"
include "cvv.mm"
include "wb.mm"
include "elex.mm"
include "cab.mm"
include "df-mea.mm"
include "eleq2i.mm"
include "a1i.mm"
include "dmeq.mm"
include "feq12d.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "pweqd.mm"
include "raleqdv.mm"
include "reseq1.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "bitrd.mm"
include "elabg.mm"
include "syl.mm"
include "mpbid.mm"
include "simplld.mm"
include "simplrd.mm"
include "simprd.mm"
include "jca31.mm"
include "fex.mm"
include "ad2antrr.mm"
include "mpbird.mm"
include "impbii.mm"

theorem ismea
  let vx: setvar x
  let vy: setvar y
  let cM: class M
  let vz: setvar z
  let vk: setvar k

  disjoint M x
  disjoint x y
  disjoint M z
  disjoint x z
  disjoint y z
  disjoint k x
  assert |- ( M e. Meas <-> ( ( ( M : dom M --> ( 0 [,] +oo ) /\ dom M e. SAlg ) /\ ( M ` (/) ) = 0 ) /\ A. x e. ~P dom M ( ( x ~<_ _om /\ Disj_ y e. x y ) -> ( M ` U. x ) = ( sum^ ` ( M |` x ) ) ) ) )

  proof
    cM
    cmea
    wcel
    #
    cM
    cdm
    #
    cc0
    cpnf
    cicc
    co
    #
    cM
    wf
    #
    @1
    csalg
    wcel
    #
    wa
    #
    c0
    cM
    cfv
    #
    cc0
    wceq
    #
    wa
    #
    vx
    cv
    #
    com
    cdom
    wbr
    vy
    @9
    vy
    cv
    wdisj
    wa
    #
    @9
    cuni
    #
    cM
    cfv
    #
    cM
    @9
    cres
    #
    csumge0
    cfv
    #
    wceq
    #
    wi
    #
    vx
    @1
    cpw
    #
    wral
    #
    wa
    #
    @0
    @5
    @7
    @18
    @0
    @5
    @7
    @18
    @0
    @0
    @19
    @0
    id
    @0
    cM
    cvv
    wcel
    #
    @0
    @19
    wb
    #
    cM
    cmea
    elex
    @20
    @0
    cM
    vz
    cv
    #
    cdm
    #
    @2
    @22
    wf
    #
    @23
    csalg
    wcel
    #
    wa
    #
    c0
    @22
    cfv
    #
    cc0
    wceq
    #
    wa
    #
    @10
    @11
    @22
    cfv
    #
    @22
    @9
    cres
    #
    csumge0
    cfv
    #
    wceq
    #
    wi
    #
    vx
    @23
    cpw
    #
    wral
    #
    wa
    #
    vz
    cab
    #
    wcel
    #
    @19
    @0
    @39
    wb
    @20
    cmea
    @38
    cM
    vz
    vx
    vy
    df-mea
    eleq2i
    a1i
    @37
    @19
    vz
    cM
    cvv
    @22
    cM
    wceq
    #
    @29
    @8
    @36
    @18
    @40
    @26
    @5
    @28
    @7
    @40
    @24
    @3
    @25
    @4
    @40
    @23
    @1
    @2
    @22
    cM
    @40
    id
    @22
    cM
    dmeq
    #
    feq12d
    @40
    @23
    @1
    csalg
    @41
    eleq1d
    anbi12d
    @40
    @27
    @6
    cc0
    c0
    @22
    cM
    fveq1
    eqeq1d
    anbi12d
    @40
    @36
    @34
    vx
    @17
    wral
    @18
    @40
    @34
    vx
    @35
    @17
    @40
    @23
    @1
    @41
    pweqd
    raleqdv
    @40
    @34
    @16
    vx
    @17
    @40
    @33
    @15
    @10
    @40
    @30
    @12
    @32
    @14
    @11
    @22
    cM
    fveq1
    @40
    @31
    @13
    csumge0
    @22
    cM
    @9
    reseq1
    fveq2d
    eqeq12d
    imbi2d
    ralbidv
    bitrd
    anbi12d
    elabg
    bitrd
    #
    syl
    mpbid
    #
    simplld
    @0
    @5
    @7
    @18
    @43
    simplrd
    @0
    @8
    @18
    @43
    simprd
    jca31
    @19
    @0
    @19
    @19
    id
    @5
    @21
    @7
    @18
    @5
    @20
    @21
    @1
    @2
    csalg
    cM
    fex
    @42
    syl
    ad2antrr
    mpbird
    impbii
end
