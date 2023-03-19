include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "c1st.mm"
include "ccom.mm"
include "csn.mm"
include "cxp.mm"
include "cseq.mm"
include "cop.mm"
include "cuz.mm"
include "cfv.mm"
include "wfn.mm"
include "seqfn.mm"
include "adantr.mm"
include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "seq1.mm"
include "id.mm"
include "uzid.mm"
include "syl6eleqr.mm"
include "fvconst2g.mm"
include "syl2anr.mm"
include "fvsng.mm"
include "eqtr4d.mm"
include "ex.mm"
include "wb.mm"
include "seqp1.mm"
include "fvex.mm"
include "algrflem.mm"
include "syl6eq.mm"
include "adantl.mm"
include "syl5ibr.mm"
include "expcom.mm"
include "a2d.mm"
include "uzind4.mm"
include "impcom.mm"
include "adantll.mm"
include "eqfnfvd.mm"
include "syl5eq.mm"

theorem seq1st
  let cA: class A
  let cR: class R
  let cF: class F
  let cM: class M
  let cV: class V
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let wph: wff ph
  let cS: class S
  assume algrf.1: |- Z = ( ZZ>= ` M )
  assume algrf.2: |- R = seq M ( ( F o. 1st ) , ( Z X. { A } ) )


  assert |- ( ( M e. ZZ /\ A e. V ) -> R = seq M ( ( F o. 1st ) , { <. M , A >. } ) )

  proof
    cM
    cz
    wcel
    #
    cA
    cV
    wcel
    #
    wa
    #
    cR
    cF
    c1st
    ccom
    #
    cZ
    cA
    csn
    cxp
    #
    cM
    cseq
    #
    @3
    cM
    cA
    cop
    csn
    #
    cM
    cseq
    #
    algrf.2
    @2
    vx
    cM
    cuz
    cfv
    #
    @5
    @7
    @0
    @5
    @8
    wfn
    @1
    @3
    @4
    cM
    seqfn
    adantr
    @0
    @7
    @8
    wfn
    @1
    @3
    @6
    cM
    seqfn
    adantr
    @1
    vx
    cv
    #
    @8
    wcel
    #
    @9
    @5
    cfv
    #
    @9
    @7
    cfv
    #
    wceq
    #
    @0
    @10
    @1
    @13
    @1
    vy
    cv
    #
    @5
    cfv
    #
    @14
    @7
    cfv
    #
    wceq
    #
    wi
    @1
    cM
    @5
    cfv
    #
    cM
    @7
    cfv
    #
    wceq
    #
    wi
    @1
    @13
    wi
    #
    @1
    @9
    c1
    caddc
    co
    #
    @5
    cfv
    #
    @22
    @7
    cfv
    #
    wceq
    #
    wi
    @21
    vy
    vx
    cM
    @9
    @14
    cM
    wceq
    #
    @17
    @20
    @1
    @26
    @15
    @18
    @16
    @19
    @14
    cM
    @5
    fveq2
    @14
    cM
    @7
    fveq2
    eqeq12d
    imbi2d
    @14
    @9
    wceq
    #
    @17
    @13
    @1
    @27
    @15
    @11
    @16
    @12
    @14
    @9
    @5
    fveq2
    @14
    @9
    @7
    fveq2
    eqeq12d
    imbi2d
    #
    @14
    @22
    wceq
    #
    @17
    @25
    @1
    @29
    @15
    @23
    @16
    @24
    @14
    @22
    @5
    fveq2
    @14
    @22
    @7
    fveq2
    eqeq12d
    imbi2d
    @28
    @0
    @1
    @20
    @2
    @18
    cM
    @4
    cfv
    #
    @19
    @0
    @18
    @30
    wceq
    @1
    @3
    @4
    cM
    seq1
    adantr
    @2
    @19
    cM
    @6
    cfv
    #
    @30
    @0
    @19
    @31
    wceq
    @1
    @3
    @6
    cM
    seq1
    adantr
    @2
    @30
    cA
    @31
    @1
    @1
    cM
    cZ
    wcel
    @30
    cA
    wceq
    @0
    @1
    id
    @0
    cM
    @8
    cZ
    cM
    uzid
    algrf.1
    syl6eleqr
    cZ
    cA
    cM
    cV
    fvconst2g
    syl2anr
    cM
    cA
    cz
    cV
    fvsng
    eqtr4d
    eqtr4d
    eqtr4d
    ex
    @10
    @1
    @13
    @25
    @1
    @10
    @13
    @25
    wi
    @13
    @25
    @1
    @10
    wa
    @11
    cF
    cfv
    #
    @12
    cF
    cfv
    #
    wceq
    #
    @11
    @12
    cF
    fveq2
    @10
    @25
    @34
    wb
    @1
    @10
    @23
    @32
    @24
    @33
    @10
    @23
    @11
    @22
    @4
    cfv
    #
    @3
    co
    @32
    @3
    @4
    cM
    @9
    seqp1
    @11
    @35
    cF
    @9
    @5
    fvex
    @22
    @4
    fvex
    algrflem
    syl6eq
    @10
    @24
    @12
    @22
    @6
    cfv
    #
    @3
    co
    @33
    @3
    @6
    cM
    @9
    seqp1
    @12
    @36
    cF
    @9
    @7
    fvex
    @22
    @6
    fvex
    algrflem
    syl6eq
    eqeq12d
    adantl
    syl5ibr
    expcom
    a2d
    uzind4
    impcom
    adantll
    eqfnfvd
    syl5eq
end
