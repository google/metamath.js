include "clmhm.mm"
include "co.mm"
include "wcel.mm"
include "clnm.mm"
include "crn.mm"
include "wceq.mm"
include "w3a.mm"
include "clmod.mm"
include "cv.mm"
include "cress.mm"
include "clfig.mm"
include "clss.mm"
include "cfv.mm"
include "wral.mm"
include "lmhmlmod2.mm"
include "3ad2ant1.mm"
include "wa.mm"
include "ccnv.mm"
include "cima.mm"
include "cbs.mm"
include "wfo.mm"
include "wss.mm"
include "wf.mm"
include "eqid.mm"
include "lmhmf.mm"
include "simp3.mm"
include "dffo2.mm"
include "sylanbrc.mm"
include "lssss.mm"
include "foimacnv.mm"
include "syl2an.mm"
include "oveq2d.mm"
include "simpl2.mm"
include "lmhmpreima.mm"
include "3ad2antl1.mm"
include "lnmlssfg.mm"
include "syl2anc.mm"
include "simpl1.mm"
include "lmhmfgima.mm"
include "eqeltrrd.mm"
include "ralrimiva.mm"
include "islnm.mm"

theorem lnmepi
  let cB: class B
  let cS: class S
  let cT: class T
  let cF: class F
  let va: setvar a
  assume lnmepi.b: |- B = ( Base ` T )


  assert |- ( ( F e. ( S LMHom T ) /\ S e. LNoeM /\ ran F = B ) -> T e. LNoeM )

  proof
    cF
    cS
    cT
    clmhm
    co
    wcel
    #
    cS
    clnm
    wcel
    #
    cF
    crn
    cB
    wceq
    #
    w3a
    #
    cT
    clmod
    wcel
    #
    cT
    va
    cv
    #
    cress
    co
    #
    clfig
    wcel
    #
    va
    cT
    clss
    cfv
    #
    wral
    cT
    clnm
    wcel
    @0
    @1
    @4
    @2
    cS
    cT
    cF
    lmhmlmod2
    3ad2ant1
    @3
    @7
    va
    @8
    @3
    @5
    @8
    wcel
    #
    wa
    #
    cT
    cF
    cF
    ccnv
    @5
    cima
    #
    cima
    #
    cress
    co
    #
    @6
    clfig
    @10
    @12
    @5
    cT
    cress
    @3
    cS
    cbs
    cfv
    #
    cB
    cF
    wfo
    #
    @5
    cB
    wss
    @12
    @5
    wceq
    @9
    @3
    @14
    cB
    cF
    wf
    #
    @2
    @15
    @0
    @1
    @16
    @2
    @14
    cB
    cS
    cT
    cF
    @14
    eqid
    lnmepi.b
    lmhmf
    3ad2ant1
    @0
    @1
    @2
    simp3
    @14
    cB
    cF
    dffo2
    sylanbrc
    @8
    @5
    cB
    cT
    lnmepi.b
    @8
    eqid
    #
    lssss
    @14
    cB
    @5
    cF
    foimacnv
    syl2an
    oveq2d
    @10
    @11
    cS
    cT
    cS
    clss
    cfv
    #
    cF
    cS
    @11
    cress
    co
    #
    @13
    @13
    eqid
    @19
    eqid
    #
    @18
    eqid
    #
    @10
    @1
    @11
    @18
    wcel
    #
    @19
    clfig
    wcel
    @0
    @1
    @2
    @9
    simpl2
    @0
    @1
    @9
    @22
    @2
    cS
    cT
    @5
    cF
    @18
    @8
    @21
    @17
    lmhmpreima
    3ad2antl1
    #
    @19
    @18
    @11
    cS
    @21
    @20
    lnmlssfg
    syl2anc
    @23
    @0
    @1
    @2
    @9
    simpl1
    lmhmfgima
    eqeltrrd
    ralrimiva
    @8
    va
    cT
    @17
    islnm
    sylanbrc
end
