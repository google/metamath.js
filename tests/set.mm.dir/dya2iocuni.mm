include "ctx.mm"
include "co.mm"
include "wcel.mm"
include "wel.mm"
include "cv.mm"
include "wss.mm"
include "wa.mm"
include "wrex.mm"
include "crn.mm"
include "crab.mm"
include "cpw.mm"
include "cuni.mm"
include "wceq.mm"
include "ssrab2.mm"
include "cxp.mm"
include "wfn.mm"
include "cvv.mm"
include "dya2iocrfn.mm"
include "cz.mm"
include "c2.mm"
include "cexp.mm"
include "cdiv.mm"
include "c1.mm"
include "caddc.mm"
include "cico.mm"
include "cmpt2.mm"
include "zex.mm"
include "mpt2ex.mm"
include "eqeltri.mm"
include "rnex.mm"
include "xpex.mm"
include "fnex.mm"
include "mp2an.mm"
include "elpw2.mm"
include "mpbir.mm"
include "a1i.mm"
include "c0.mm"
include "wn.mm"
include "wral.mm"
include "rex0.mm"
include "rexeq.mm"
include "mtbiri.mm"
include "ralrimivw.mm"
include "rabeq0.mm"
include "sylibr.mm"
include "unieqd.mm"
include "uni0.mm"
include "syl6eq.mm"
include "0ss.mm"
include "syl6eqss.mm"
include "wne.mm"
include "elequ2.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "rexbidv.mm"
include "elrab.mm"
include "simpr.mm"
include "reximi.mm"
include "r19.9rzv.mm"
include "syl5ibr.mm"
include "adantld.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "unissb.mm"
include "pm2.61ine.mm"
include "dya2iocnei.mm"
include "simpl.mm"
include "ssel2.mm"
include "ancoms.mm"
include "adantl.mm"
include "elequ1.mm"
include "anbi1d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "jca.mm"
include "simprl.mm"
include "reximi2.mm"
include "syl.mm"
include "eluni2.mm"
include "ex.mm"
include "ssrdv.mm"
include "eqssd.mm"
include "unieq.mm"
include "eqeq1d.mm"

theorem dya2iocuni
  let vx: setvar x
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cR: class R
  let vn: setvar n
  let cI: class I
  let cJ: class J
  let vc: setvar c
  let vm: setvar m
  let vp: setvar p
  let vb: setvar b
  let vz: setvar z
  assume sxbrsiga.0: |- J = ( topGen ` ran (,) )
  assume dya2ioc.1: |- I = ( x e. ZZ , n e. ZZ |-> ( ( x / ( 2 ^ n ) ) [,) ( ( x + 1 ) / ( 2 ^ n ) ) ) )
  assume dya2ioc.2: |- R = ( u e. ran I , v e. ran I |-> ( u X. v ) )

  disjoint c u
  disjoint c v
  disjoint A c
  disjoint u v
  disjoint A u
  disjoint A v
  disjoint R c
  disjoint n x
  disjoint I x
  disjoint u v
  disjoint I u
  disjoint I v
  disjoint u x
  disjoint v x
  disjoint m p
  disjoint m x
  disjoint p x
  disjoint b c
  disjoint b m
  disjoint b p
  disjoint b u
  disjoint b v
  disjoint b z
  disjoint A b
  disjoint c m
  disjoint c p
  disjoint c z
  disjoint m u
  disjoint m v
  disjoint m z
  disjoint A m
  disjoint p u
  disjoint p v
  disjoint p z
  disjoint A p
  disjoint u z
  disjoint v z
  disjoint A z
  disjoint J m
  disjoint R b
  disjoint R m
  disjoint R p
  assert |- ( A e. ( J tX J ) -> E. c e. ~P ran R U. c = A )

  proof
    cA
    cJ
    cJ
    ctx
    co
    wcel
    #
    vz
    vb
    wel
    #
    vb
    cv
    #
    cA
    wss
    #
    wa
    #
    vz
    cA
    wrex
    #
    vb
    cR
    crn
    #
    crab
    #
    @6
    cpw
    #
    wcel
    #
    @7
    cuni
    #
    cA
    wceq
    #
    vc
    cv
    #
    cuni
    #
    cA
    wceq
    #
    vc
    @8
    wrex
    @9
    @0
    @9
    @7
    @6
    wss
    @5
    vb
    @6
    ssrab2
    @7
    @6
    cR
    cR
    cI
    crn
    #
    @15
    cxp
    #
    wfn
    @16
    cvv
    wcel
    cR
    cvv
    wcel
    vx
    vv
    vu
    cR
    vn
    cI
    cJ
    sxbrsiga.0
    dya2ioc.1
    dya2ioc.2
    dya2iocrfn
    @15
    @15
    cI
    cI
    vx
    vn
    cz
    cz
    vx
    cv
    #
    c2
    vn
    cv
    cexp
    co
    #
    cdiv
    co
    @17
    c1
    caddc
    co
    @18
    cdiv
    co
    cico
    co
    #
    cmpt2
    cvv
    dya2ioc.1
    vx
    vn
    cz
    cz
    @19
    zex
    zex
    mpt2ex
    eqeltri
    rnex
    #
    @20
    xpex
    @16
    cvv
    cR
    fnex
    mp2an
    rnex
    elpw2
    mpbir
    a1i
    @0
    @10
    cA
    @10
    cA
    wss
    #
    @0
    @21
    cA
    c0
    cA
    c0
    wceq
    #
    @10
    c0
    cA
    @22
    @10
    c0
    cuni
    c0
    @22
    @7
    c0
    @22
    @5
    wn
    #
    vb
    @6
    wral
    @7
    c0
    wceq
    @22
    @23
    vb
    @6
    @22
    @5
    @4
    vz
    c0
    wrex
    @4
    vz
    rex0
    @4
    vz
    cA
    c0
    rexeq
    mtbiri
    ralrimivw
    @5
    vb
    @6
    rabeq0
    sylibr
    unieqd
    uni0
    syl6eq
    cA
    0ss
    syl6eqss
    cA
    c0
    wne
    #
    vp
    cv
    #
    cA
    wss
    #
    vp
    @7
    wral
    @21
    @24
    @26
    vp
    @7
    @25
    @7
    wcel
    #
    @25
    @6
    wcel
    #
    vz
    vp
    wel
    #
    @26
    wa
    #
    vz
    cA
    wrex
    #
    wa
    #
    @24
    @26
    @5
    @31
    vb
    @25
    @6
    @2
    @25
    wceq
    #
    @4
    @30
    vz
    cA
    @33
    @1
    @29
    @3
    @26
    vb
    vp
    vz
    elequ2
    @2
    @25
    cA
    sseq1
    anbi12d
    rexbidv
    elrab
    #
    @24
    @31
    @26
    @28
    @31
    @26
    @24
    @26
    vz
    cA
    wrex
    @30
    @26
    vz
    cA
    @29
    @26
    simpr
    reximi
    @26
    vz
    cA
    r19.9rzv
    syl5ibr
    adantld
    syl5bi
    ralrimiv
    vp
    @7
    cA
    unissb
    sylibr
    pm2.61ine
    a1i
    @0
    vm
    cA
    @10
    @0
    vm
    cv
    #
    cA
    wcel
    #
    @35
    @10
    wcel
    #
    @0
    @36
    wa
    #
    vm
    vp
    wel
    #
    vp
    @7
    wrex
    #
    @37
    @38
    @39
    @26
    wa
    #
    vp
    @6
    wrex
    @40
    vx
    vv
    vu
    cA
    cR
    vn
    cI
    cJ
    @35
    vp
    sxbrsiga.0
    dya2ioc.1
    dya2ioc.2
    dya2iocnei
    @41
    @39
    vp
    @6
    @7
    @28
    @41
    wa
    #
    @27
    @39
    @42
    @32
    @27
    @42
    @28
    @31
    @28
    @41
    simpl
    @42
    @36
    @41
    @31
    @41
    @36
    @28
    @26
    @39
    @36
    @25
    cA
    @35
    ssel2
    ancoms
    adantl
    @28
    @41
    simpr
    @30
    @41
    vz
    @35
    cA
    vz
    cv
    @35
    wceq
    @29
    @39
    @26
    vz
    vm
    vp
    elequ1
    anbi1d
    rspcev
    syl2anc
    jca
    @34
    sylibr
    @28
    @39
    @26
    simprl
    jca
    reximi2
    syl
    vp
    @35
    @7
    eluni2
    sylibr
    ex
    ssrdv
    eqssd
    @14
    @11
    vc
    @7
    @8
    @12
    @7
    wceq
    @13
    @10
    cA
    @12
    @7
    unieq
    eqeq1d
    rspcev
    syl2anc
end
