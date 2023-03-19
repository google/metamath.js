include "cpsmet.mm"
include "cfv.mm"
include "wcel.mm"
include "cxp.mm"
include "wfn.mm"
include "crn.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wss.mm"
include "wf.mm"
include "cxr.mm"
include "psmetf.mm"
include "ffn.mm"
include "syl.mm"
include "cv.mm"
include "wral.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "ffvelrnda.mm"
include "c1st.mm"
include "c2nd.mm"
include "cop.mm"
include "wceq.mm"
include "elxp6.mm"
include "simprbi.mm"
include "psmetge0.mm"
include "3expb.mm"
include "sylan2.mm"
include "1st2nd2.mm"
include "fveq2d.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "adantl.mm"
include "breqtrrd.mm"
include "elxrge0.mm"
include "sylanbrc.mm"
include "ralrimiva.mm"
include "fnfvrnss.mm"
include "syl2anc.mm"
include "df-f.mm"

theorem psmetxrge0
  let cD: class D
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( D e. ( PsMet ` X ) -> D : ( X X. X ) --> ( 0 [,] +oo ) )

  proof
    cD
    cX
    cpsmet
    cfv
    wcel
    #
    cD
    cX
    cX
    cxp
    #
    wfn
    #
    cD
    crn
    cc0
    cpnf
    cicc
    co
    #
    wss
    #
    @1
    @3
    cD
    wf
    @0
    @1
    cxr
    cD
    wf
    @2
    cD
    cX
    psmetf
    #
    @1
    cxr
    cD
    ffn
    syl
    #
    @0
    @2
    va
    cv
    #
    cD
    cfv
    #
    @3
    wcel
    #
    va
    @1
    wral
    @4
    @6
    @0
    @9
    va
    @1
    @0
    @7
    @1
    wcel
    #
    wa
    #
    @8
    cxr
    wcel
    cc0
    @8
    cle
    wbr
    @9
    @0
    @1
    cxr
    @7
    cD
    @5
    ffvelrnda
    @11
    cc0
    @7
    c1st
    cfv
    #
    @7
    c2nd
    cfv
    #
    cD
    co
    #
    @8
    cle
    @10
    @0
    @12
    cX
    wcel
    #
    @13
    cX
    wcel
    #
    wa
    #
    cc0
    @14
    cle
    wbr
    #
    @10
    @7
    @12
    @13
    cop
    #
    wceq
    @17
    @7
    cX
    cX
    elxp6
    simprbi
    @0
    @15
    @16
    @18
    @12
    @13
    cD
    cX
    psmetge0
    3expb
    sylan2
    @10
    @8
    @14
    wceq
    @0
    @10
    @8
    @19
    cD
    cfv
    @14
    @10
    @7
    @19
    cD
    @7
    cX
    cX
    1st2nd2
    fveq2d
    @12
    @13
    cD
    df-ov
    syl6eqr
    adantl
    breqtrrd
    @8
    elxrge0
    sylanbrc
    ralrimiva
    va
    @1
    @3
    cD
    fnfvrnss
    syl2anc
    @1
    @3
    cD
    df-f
    sylanbrc
end
