include "cvv.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "c0.mm"
include "c1o.mm"
include "cop.mm"
include "com.mm"
include "cv.mm"
include "wceq.mm"
include "cxp.mm"
include "cuni.mm"
include "c1st.mm"
include "cfv.mm"
include "cif.mm"
include "cmpt2.mm"
include "wne.mm"
include "wi.mm"
include "nfv.mm"
include "nfmpt22.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfne.mm"
include "nfim.mm"
include "nfmpt21.mm"
include "1onn.mm"
include "elexi.mm"
include "co.mm"
include "df-ov.mm"
include "csb.mm"
include "0ex.mm"
include "opex.mm"
include "ifex.mm"
include "csbex.mm"
include "eqid.mm"
include "ovmpt2s.mm"
include "mp3an13.mm"
include "adantr.mm"
include "csbeq1a.mm"
include "sylan9eqr.mm"
include "adantl.mm"
include "eleq1.mm"
include "notbid.mm"
include "biimprcd.mm"
include "pm3.14.mm"
include "olcs.mm"
include "syl6.mm"
include "iffalse.mm"
include "imp.mm"
include "wo.mm"
include "ifeqor.mm"
include "vuniex.mm"
include "fvex.mm"
include "opnzi.mm"
include "neii.mm"
include "eqeq1.mm"
include "mtbiri.mm"
include "vex.mm"
include "jaoi.mm"
include "mp1i.mm"
include "neqned.mm"
include "eqnetrd.mm"
include "adantrl.mm"
include "eqnetrrd.mm"
include "syl5eqner.mm"
include "ancom2s.mm"
include "an12s.mm"
include "exp31.mm"
include "vtoclef.mm"
include "vtoclefex.mm"
include "anabsi5.mm"
include "necomd.mm"
include "neneqd.mm"

theorem finxpreclem2
  let vx: setvar x
  let cU: class U
  let vn: setvar n
  let cX: class X

  disjoint U n
  disjoint U x
  disjoint n x
  disjoint X n
  disjoint X x
  assert |- ( ( X e. _V /\ -. X e. U ) -> -. (/) = ( ( n e. _om , x e. _V |-> if ( ( n = 1o /\ x e. U ) , (/) , if ( x e. ( _V X. U ) , <. U. n , ( 1st ` x ) >. , <. n , x >. ) ) ) ` <. 1o , X >. ) )

  proof
    cX
    cvv
    wcel
    #
    cX
    cU
    wcel
    #
    wn
    #
    wa
    #
    c0
    c1o
    cX
    cop
    #
    vn
    vx
    com
    cvv
    vn
    cv
    #
    c1o
    wceq
    #
    vx
    cv
    #
    cU
    wcel
    #
    wa
    #
    c0
    @7
    cvv
    cU
    cxp
    wcel
    #
    @5
    cuni
    #
    @7
    c1st
    cfv
    #
    cop
    #
    @5
    @7
    cop
    #
    cif
    #
    cif
    #
    cmpt2
    #
    cfv
    #
    @3
    @18
    c0
    @0
    @2
    @18
    c0
    wne
    #
    @3
    @19
    wi
    #
    vx
    cX
    cvv
    @3
    @19
    vx
    @3
    vx
    nfv
    vx
    @18
    c0
    vx
    @4
    @17
    vn
    vx
    com
    cvv
    @16
    nfmpt22
    vx
    @4
    nfcv
    nffv
    vx
    c0
    nfcv
    nfne
    nfim
    @7
    cX
    wceq
    #
    @20
    wi
    vn
    c1o
    @21
    @20
    vn
    @21
    vn
    nfv
    @3
    @19
    vn
    @3
    vn
    nfv
    vn
    @18
    c0
    vn
    @4
    @17
    vn
    vx
    com
    cvv
    @16
    nfmpt21
    vn
    @4
    nfcv
    nffv
    vn
    c0
    nfcv
    nfne
    nfim
    nfim
    c1o
    com
    1onn
    elexi
    @6
    @21
    @3
    @19
    @0
    @6
    @21
    wa
    #
    @2
    @19
    @0
    @2
    @22
    @19
    @0
    @2
    @22
    wa
    #
    wa
    #
    @18
    c1o
    cX
    @17
    co
    #
    c0
    c1o
    cX
    @17
    df-ov
    @24
    @25
    vn
    c1o
    vx
    cX
    @16
    csb
    #
    csb
    #
    c0
    @0
    @25
    @27
    wceq
    #
    @23
    c1o
    com
    wcel
    @0
    @27
    cvv
    wcel
    @28
    1onn
    vn
    c1o
    @26
    vx
    cX
    @16
    @9
    c0
    @15
    0ex
    @10
    @13
    @14
    @11
    @12
    opex
    @5
    @7
    opex
    ifex
    ifex
    csbex
    csbex
    vn
    vx
    c1o
    cX
    com
    cvv
    @16
    @17
    cvv
    @17
    eqid
    ovmpt2s
    mp3an13
    adantr
    @23
    @27
    c0
    wne
    @0
    @23
    @16
    @27
    c0
    @22
    @16
    @27
    wceq
    @2
    @21
    @6
    @16
    @26
    @27
    vx
    cX
    @16
    csbeq1a
    vn
    c1o
    @26
    csbeq1a
    sylan9eqr
    adantl
    @2
    @21
    @16
    c0
    wne
    @6
    @2
    @21
    wa
    #
    @16
    @15
    c0
    @2
    @21
    @16
    @15
    wceq
    #
    @2
    @21
    @9
    wn
    #
    @30
    @2
    @21
    @8
    wn
    #
    @31
    @21
    @32
    @2
    @21
    @8
    @1
    @7
    cX
    cU
    eleq1
    notbid
    biimprcd
    @6
    wn
    @32
    @31
    @6
    @8
    pm3.14
    olcs
    syl6
    @9
    c0
    @15
    iffalse
    syl6
    imp
    @29
    @15
    c0
    @15
    @13
    wceq
    #
    @15
    @14
    wceq
    #
    wo
    @15
    c0
    wceq
    #
    wn
    #
    @29
    @10
    @13
    @14
    ifeqor
    @33
    @36
    @34
    @33
    @35
    @13
    c0
    wceq
    @13
    c0
    @11
    @12
    vn
    vuniex
    @7
    c1st
    fvex
    opnzi
    neii
    @15
    @13
    c0
    eqeq1
    mtbiri
    @34
    @35
    @14
    c0
    wceq
    @14
    c0
    @5
    @7
    vn
    vex
    vx
    vex
    opnzi
    neii
    @15
    @14
    c0
    eqeq1
    mtbiri
    jaoi
    mp1i
    neqned
    eqnetrd
    adantrl
    eqnetrrd
    adantl
    eqnetrd
    syl5eqner
    ancom2s
    an12s
    exp31
    vtoclef
    vtoclefex
    anabsi5
    necomd
    neneqd
end
