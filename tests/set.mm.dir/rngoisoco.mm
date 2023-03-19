include "crngo.mm"
include "wcel.mm"
include "w3a.mm"
include "crngiso.mm"
include "co.mm"
include "wa.mm"
include "ccom.mm"
include "crnghom.mm"
include "c1st.mm"
include "cfv.mm"
include "crn.mm"
include "wf1o.mm"
include "rngoisohom.mm"
include "3expa.mm"
include "3adantl3.mm"
include "3adantl1.mm"
include "anim12da.mm"
include "rngohomco.mm"
include "syldan.mm"
include "eqid.mm"
include "rngoiso1o.mm"
include "adantrl.mm"
include "adantrr.mm"
include "f1oco.mm"
include "syl2anc.mm"
include "wb.mm"
include "isrngoiso.mm"
include "3adant2.mm"
include "adantr.mm"
include "mpbir2and.mm"

theorem rngoisoco
  let cR: class R
  let cS: class S
  let cT: class T
  let cF: class F
  let cG: class G


  assert |- ( ( ( R e. RingOps /\ S e. RingOps /\ T e. RingOps ) /\ ( F e. ( R RngIso S ) /\ G e. ( S RngIso T ) ) ) -> ( G o. F ) e. ( R RngIso T ) )

  proof
    cR
    crngo
    wcel
    #
    cS
    crngo
    wcel
    #
    cT
    crngo
    wcel
    #
    w3a
    #
    cF
    cR
    cS
    crngiso
    co
    wcel
    #
    cG
    cS
    cT
    crngiso
    co
    wcel
    #
    wa
    #
    wa
    #
    cG
    cF
    ccom
    #
    cR
    cT
    crngiso
    co
    wcel
    #
    @8
    cR
    cT
    crnghom
    co
    wcel
    #
    cR
    c1st
    cfv
    #
    crn
    #
    cT
    c1st
    cfv
    #
    crn
    #
    @8
    wf1o
    #
    @3
    @6
    cF
    cR
    cS
    crnghom
    co
    wcel
    #
    cG
    cS
    cT
    crnghom
    co
    wcel
    #
    wa
    @10
    @3
    @4
    @5
    @16
    @17
    @0
    @1
    @4
    @16
    @2
    @0
    @1
    @4
    @16
    cR
    cS
    cF
    rngoisohom
    3expa
    3adantl3
    @1
    @2
    @5
    @17
    @0
    @1
    @2
    @5
    @17
    cS
    cT
    cG
    rngoisohom
    3expa
    3adantl1
    anim12da
    cR
    cS
    cT
    cF
    cG
    rngohomco
    syldan
    @7
    cS
    c1st
    cfv
    #
    crn
    #
    @14
    cG
    wf1o
    #
    @12
    @19
    cF
    wf1o
    #
    @15
    @3
    @5
    @20
    @4
    @1
    @2
    @5
    @20
    @0
    @1
    @2
    @5
    @20
    cS
    cT
    cG
    @18
    @13
    @19
    @14
    @18
    eqid
    #
    @19
    eqid
    #
    @13
    eqid
    #
    @14
    eqid
    #
    rngoiso1o
    3expa
    3adantl1
    adantrl
    @3
    @4
    @21
    @5
    @0
    @1
    @4
    @21
    @2
    @0
    @1
    @4
    @21
    cR
    cS
    cF
    @11
    @18
    @12
    @19
    @11
    eqid
    #
    @12
    eqid
    #
    @22
    @23
    rngoiso1o
    3expa
    3adantl3
    adantrr
    @12
    @19
    @14
    cG
    cF
    f1oco
    syl2anc
    @3
    @9
    @10
    @15
    wa
    wb
    #
    @6
    @0
    @2
    @28
    @1
    cR
    cT
    @8
    @11
    @13
    @12
    @14
    @26
    @27
    @24
    @25
    isrngoiso
    3adant2
    adantr
    mpbir2and
end
