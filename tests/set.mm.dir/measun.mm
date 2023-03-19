include "cmeas.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "w3a.mm"
include "cun.mm"
include "cdif.mm"
include "cxad.mm"
include "co.mm"
include "wss.mm"
include "simp1.mm"
include "csiga.mm"
include "crn.mm"
include "cuni.mm"
include "measbase.mm"
include "3ad2ant1.mm"
include "simp2l.mm"
include "simp2r.mm"
include "unelsiga.mm"
include "syl3anc.mm"
include "ssun2.mm"
include "a1i.mm"
include "measxun2.mm"
include "syl121anc.mm"
include "difun2.mm"
include "inundif.mm"
include "uneq1.mm"
include "uncom.mm"
include "un0.mm"
include "eqtri.mm"
include "syl6eq.mm"
include "syl5reqr.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "3ad2ant3.mm"
include "cxr.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "iccssxr.mm"
include "measvxrge0.mm"
include "sseldi.mm"
include "syl2anc.mm"
include "xaddcom.mm"
include "3eqtrd.mm"

theorem measun
  let cA: class A
  let cB: class B
  let cS: class S
  let cM: class M


  assert |- ( ( M e. ( measures ` S ) /\ ( A e. S /\ B e. S ) /\ ( A i^i B ) = (/) ) -> ( M ` ( A u. B ) ) = ( ( M ` A ) +e ( M ` B ) ) )

  proof
    cM
    cS
    cmeas
    cfv
    wcel
    #
    cA
    cS
    wcel
    #
    cB
    cS
    wcel
    #
    wa
    #
    cA
    cB
    cin
    #
    c0
    wceq
    #
    w3a
    #
    cA
    cB
    cun
    #
    cM
    cfv
    #
    cB
    cM
    cfv
    #
    @7
    cB
    cdif
    #
    cM
    cfv
    #
    cxad
    co
    #
    @9
    cA
    cM
    cfv
    #
    cxad
    co
    #
    @13
    @9
    cxad
    co
    #
    @6
    @0
    @7
    cS
    wcel
    #
    @2
    cB
    @7
    wss
    #
    @8
    @12
    wceq
    @0
    @3
    @5
    simp1
    #
    @6
    cS
    csiga
    crn
    cuni
    wcel
    #
    @1
    @2
    @16
    @0
    @3
    @19
    @5
    cS
    cM
    measbase
    3ad2ant1
    @0
    @1
    @2
    @5
    simp2l
    #
    @0
    @1
    @2
    @5
    simp2r
    #
    cA
    cB
    cS
    unelsiga
    syl3anc
    @21
    @17
    @6
    cB
    cA
    ssun2
    a1i
    @7
    cB
    cS
    cM
    measxun2
    syl121anc
    @5
    @0
    @12
    @14
    wceq
    @3
    @5
    @11
    @13
    @9
    cxad
    @5
    @10
    cA
    cM
    @5
    @10
    cA
    cB
    cdif
    #
    cA
    cA
    cB
    difun2
    @5
    cA
    @4
    @22
    cun
    #
    @22
    cA
    cB
    inundif
    @5
    @23
    c0
    @22
    cun
    #
    @22
    @4
    c0
    @22
    uneq1
    @24
    @22
    c0
    cun
    @22
    c0
    @22
    uncom
    @22
    un0
    eqtri
    syl6eq
    syl5reqr
    syl5eq
    fveq2d
    oveq2d
    3ad2ant3
    @6
    @9
    cxr
    wcel
    #
    @13
    cxr
    wcel
    #
    @14
    @15
    wceq
    @6
    @0
    @2
    @25
    @18
    @21
    @0
    @2
    wa
    cc0
    cpnf
    cicc
    co
    #
    cxr
    @9
    cc0
    cpnf
    iccssxr
    #
    cB
    cS
    cM
    measvxrge0
    sseldi
    syl2anc
    @6
    @0
    @1
    @26
    @18
    @20
    @0
    @1
    wa
    @27
    cxr
    @13
    @28
    cA
    cS
    cM
    measvxrge0
    sseldi
    syl2anc
    @9
    @13
    xaddcom
    syl2anc
    3eqtrd
end
