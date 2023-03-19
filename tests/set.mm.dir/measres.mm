include "cmeas.mm"
include "cfv.mm"
include "wcel.mm"
include "csiga.mm"
include "crn.mm"
include "cuni.mm"
include "wss.mm"
include "w3a.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "cres.mm"
include "wf.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wdisj.mm"
include "wa.mm"
include "cesum.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "simp2.mm"
include "measfrge0.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "fssresd.mm"
include "0elsiga.mm"
include "fvres.mm"
include "3syl.mm"
include "measvnul.mm"
include "eqtrd.mm"
include "simp11.mm"
include "simp13.mm"
include "sspwb.mm"
include "ssel2.mm"
include "sylanb.mm"
include "syl2anc.mm"
include "measvun.mm"
include "syl3anc.mm"
include "simp3l.mm"
include "sigaclcu.mm"
include "syl.mm"
include "elpwi.mm"
include "sselda.mm"
include "adantll.mm"
include "esumeq2dv.mm"
include "3adant3.mm"
include "3eqtr4d.mm"
include "3expia.mm"
include "ralrimiva.mm"
include "3jca.mm"
include "ismeas.mm"
include "biimprd.mm"
include "sylc.mm"

theorem measres
  let cS: class S
  let cT: class T
  let cM: class M
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( M e. ( measures ` S ) /\ T e. U. ran sigAlgebra /\ T C_ S ) -> ( M |` T ) e. ( measures ` T ) )

  proof
    cM
    cS
    cmeas
    cfv
    wcel
    #
    cT
    csiga
    crn
    cuni
    wcel
    #
    cT
    cS
    wss
    #
    w3a
    #
    @1
    cT
    cc0
    cpnf
    cicc
    co
    #
    cM
    cT
    cres
    #
    wf
    #
    c0
    @5
    cfv
    #
    cc0
    wceq
    #
    vx
    cv
    #
    com
    cdom
    wbr
    #
    vy
    @9
    vy
    cv
    #
    wdisj
    #
    wa
    #
    @9
    cuni
    #
    @5
    cfv
    #
    @9
    @11
    @5
    cfv
    #
    vy
    cesum
    #
    wceq
    #
    wi
    #
    vx
    cT
    cpw
    #
    wral
    #
    w3a
    #
    @5
    cT
    cmeas
    cfv
    wcel
    #
    @0
    @1
    @2
    simp2
    #
    @3
    @6
    @8
    @21
    @3
    cS
    @4
    cT
    cM
    @0
    @1
    cS
    @4
    cM
    wf
    @2
    cS
    cM
    measfrge0
    3ad2ant1
    @0
    @1
    @2
    simp3
    fssresd
    @3
    @7
    c0
    cM
    cfv
    #
    cc0
    @3
    @1
    c0
    cT
    wcel
    @7
    @25
    wceq
    @24
    cT
    0elsiga
    c0
    cT
    cM
    fvres
    3syl
    @0
    @1
    @25
    cc0
    wceq
    @2
    cS
    cM
    measvnul
    3ad2ant1
    eqtrd
    @3
    @19
    vx
    @20
    @3
    @9
    @20
    wcel
    #
    @13
    @18
    @3
    @26
    @13
    w3a
    #
    @14
    cM
    cfv
    #
    @9
    @11
    cM
    cfv
    #
    vy
    cesum
    #
    @15
    @17
    @27
    @0
    @9
    cS
    cpw
    #
    wcel
    #
    @13
    @28
    @30
    wceq
    @0
    @1
    @2
    @26
    @13
    simp11
    @27
    @2
    @26
    @32
    @0
    @1
    @2
    @26
    @13
    simp13
    @3
    @26
    @13
    simp2
    #
    @2
    @20
    @31
    wss
    @26
    @32
    cT
    cS
    sspwb
    @20
    @31
    @9
    ssel2
    sylanb
    syl2anc
    @3
    @26
    @13
    simp3
    vy
    @9
    cS
    cM
    measvun
    syl3anc
    @27
    @14
    cT
    wcel
    #
    @15
    @28
    wceq
    @27
    @1
    @26
    @10
    @34
    @3
    @26
    @1
    @13
    @24
    3ad2ant1
    @33
    @3
    @26
    @10
    @12
    simp3l
    @9
    cT
    sigaclcu
    syl3anc
    @14
    cT
    cM
    fvres
    syl
    @3
    @26
    @17
    @30
    wceq
    @13
    @3
    @26
    wa
    #
    @9
    @16
    @29
    vy
    @35
    @11
    @9
    wcel
    #
    wa
    @11
    cT
    wcel
    #
    @16
    @29
    wceq
    @26
    @36
    @37
    @3
    @26
    @9
    cT
    @11
    @9
    cT
    elpwi
    sselda
    adantll
    @11
    cT
    cM
    fvres
    syl
    esumeq2dv
    3adant3
    3eqtr4d
    3expia
    ralrimiva
    3jca
    @1
    @23
    @22
    vx
    vy
    cT
    @5
    ismeas
    biimprd
    sylc
end
