include "cv.mm"
include "cdm.mm"
include "cdif.mm"
include "wcel.mm"
include "cpred.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "wfn.mm"
include "wss.mm"
include "wral.mm"
include "cfv.mm"
include "cres.mm"
include "w3a.mm"
include "wex.mm"
include "cab.mm"
include "csn.mm"
include "cun.mm"
include "cvv.mm"
include "wfrlem10.mm"
include "wse.mm"
include "eldifi.mm"
include "setlikespec.mm"
include "sylancl.mm"
include "adantr.mm"
include "eqeltrrd.mm"
include "snex.mm"
include "unexg.mm"
include "wfrlem13.mm"
include "wfrdmss.mm"
include "snssd.mm"
include "unss.mm"
include "biimpi.mm"
include "sylancr.mm"
include "weq.mm"
include "wo.mm"
include "elun.mm"
include "velsn.mm"
include "orbi2i.mm"
include "bitri.mm"
include "wi.mm"
include "wfrdmcl.mm"
include "ssun3.mm"
include "syl.mm"
include "a1i.mm"
include "ssun1.mm"
include "syl6eqss.mm"
include "predeq3.mm"
include "sseq1d.mm"
include "syl5ibrcom.mm"
include "jaod.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "jca.mm"
include "wfrlem14.mm"
include "3jca.mm"
include "fneq2.mm"
include "sseq1.mm"
include "sseq2.mm"
include "raleqbi1dv.mm"
include "anbi12d.mm"
include "raleq.mm"
include "3anbi123d.mm"
include "spcegv.mm"
include "sylc.mm"
include "wb.mm"
include "mpan2.mm"
include "fnex.mm"
include "sylan2.mm"
include "syl2anc.mm"
include "fneq1.mm"
include "fveq1.mm"
include "reseq1.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "ralbidv.mm"
include "3anbi13d.mm"
include "exbidv.mm"
include "elabg.mm"
include "mpbird.mm"

theorem wfrlem15
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cC: class C
  let cR: class R
  let vf: setvar f
  let cF: class F
  let cG: class G
  assume wfrlem13.1: |- R We A
  assume wfrlem13.2: |- R Se A
  assume wfrlem13.3: |- F = wrecs ( R , A , G )
  assume wfrlem13.4: |- C = ( F u. { <. z , ( G ` ( F |` Pred ( R , A , z ) ) ) >. } )

  disjoint A f
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint F f
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint G f
  disjoint G x
  disjoint G y
  disjoint R f
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint C f
  disjoint C x
  disjoint C y
  assert |- ( ( z e. ( A \ dom F ) /\ Pred ( R , ( A \ dom F ) , z ) = (/) ) -> C e. { f | E. x ( f Fn x /\ ( x C_ A /\ A. y e. x Pred ( R , A , y ) C_ x ) /\ A. y e. x ( f ` y ) = ( G ` ( f |` Pred ( R , A , y ) ) ) ) } )

  proof
    vz
    cv
    #
    cA
    cF
    cdm
    #
    cdif
    #
    wcel
    #
    @2
    cR
    @0
    cpred
    c0
    wceq
    #
    wa
    #
    cC
    vf
    cv
    #
    vx
    cv
    #
    wfn
    #
    @7
    cA
    wss
    #
    cA
    cR
    vy
    cv
    #
    cpred
    #
    @7
    wss
    #
    vy
    @7
    wral
    #
    wa
    #
    @10
    @6
    cfv
    #
    @6
    @11
    cres
    #
    cG
    cfv
    #
    wceq
    #
    vy
    @7
    wral
    #
    w3a
    #
    vx
    wex
    #
    vf
    cab
    wcel
    #
    cC
    @7
    wfn
    #
    @14
    @10
    cC
    cfv
    #
    cC
    @11
    cres
    #
    cG
    cfv
    #
    wceq
    #
    vy
    @7
    wral
    #
    w3a
    #
    vx
    wex
    #
    @5
    @1
    @0
    csn
    #
    cun
    #
    cvv
    wcel
    #
    cC
    @32
    wfn
    #
    @32
    cA
    wss
    #
    @11
    @32
    wss
    #
    vy
    @32
    wral
    #
    wa
    #
    @27
    vy
    @32
    wral
    #
    w3a
    #
    @30
    @5
    @1
    cvv
    wcel
    #
    @31
    cvv
    wcel
    #
    @33
    @5
    cA
    cR
    @0
    cpred
    #
    @1
    cvv
    vz
    cA
    cR
    cF
    cG
    wfrlem13.1
    wfrlem13.3
    wfrlem10
    #
    @3
    @43
    cvv
    wcel
    #
    @4
    @3
    @0
    cA
    wcel
    cA
    cR
    wse
    @45
    @0
    cA
    @1
    eldifi
    #
    wfrlem13.2
    cA
    cR
    @0
    setlikespec
    sylancl
    adantr
    eqeltrrd
    #
    @0
    snex
    #
    @1
    @31
    cvv
    cvv
    unexg
    #
    sylancl
    @5
    @34
    @38
    @39
    @3
    @34
    @4
    vz
    cA
    cC
    cR
    cF
    cG
    wfrlem13.1
    wfrlem13.2
    wfrlem13.3
    wfrlem13.4
    wfrlem13
    adantr
    #
    @5
    @35
    @37
    @3
    @35
    @4
    @3
    @1
    cA
    wss
    #
    @31
    cA
    wss
    #
    @35
    cA
    cR
    cF
    cG
    wfrlem13.3
    wfrdmss
    @3
    @0
    cA
    @46
    snssd
    @51
    @52
    wa
    @35
    @1
    @31
    cA
    unss
    biimpi
    sylancr
    adantr
    @5
    @36
    vy
    @32
    @10
    @32
    wcel
    #
    @10
    @1
    wcel
    #
    vy
    vz
    weq
    #
    wo
    #
    @5
    @36
    @53
    @54
    @10
    @31
    wcel
    #
    wo
    @56
    @10
    @1
    @31
    elun
    @57
    @55
    @54
    vy
    @0
    velsn
    orbi2i
    bitri
    @5
    @54
    @36
    @55
    @54
    @36
    wi
    @5
    @54
    @11
    @1
    wss
    @36
    cA
    cR
    cF
    cG
    @10
    wfrlem13.3
    wfrdmcl
    @11
    @1
    @31
    ssun3
    syl
    a1i
    @5
    @36
    @55
    @43
    @32
    wss
    @5
    @43
    @1
    @32
    @44
    @1
    @31
    ssun1
    syl6eqss
    @55
    @11
    @43
    @32
    cA
    cR
    @10
    @0
    predeq3
    sseq1d
    syl5ibrcom
    jaod
    syl5bi
    ralrimiv
    jca
    @3
    @39
    @4
    @3
    @27
    vy
    @32
    vy
    vz
    cA
    cC
    cR
    cF
    cG
    wfrlem13.1
    wfrlem13.2
    wfrlem13.3
    wfrlem13.4
    wfrlem14
    ralrimiv
    adantr
    3jca
    @29
    @40
    vx
    @32
    cvv
    @7
    @32
    wceq
    #
    @23
    @34
    @14
    @38
    @28
    @39
    @7
    @32
    cC
    fneq2
    @58
    @9
    @35
    @13
    @37
    @7
    @32
    cA
    sseq1
    @12
    @36
    vy
    @7
    @32
    @7
    @32
    @11
    sseq2
    raleqbi1dv
    anbi12d
    @27
    vy
    @7
    @32
    raleq
    3anbi123d
    spcegv
    sylc
    @5
    cC
    cvv
    wcel
    #
    @22
    @30
    wb
    @5
    @34
    @41
    @59
    @50
    @47
    @41
    @34
    @33
    @59
    @41
    @42
    @33
    @48
    @49
    mpan2
    @32
    cvv
    cC
    fnex
    sylan2
    syl2anc
    @21
    @30
    vf
    cC
    cvv
    @6
    cC
    wceq
    #
    @20
    @29
    vx
    @60
    @8
    @23
    @19
    @28
    @14
    @7
    @6
    cC
    fneq1
    @60
    @18
    @27
    vy
    @7
    @60
    @15
    @24
    @17
    @26
    @10
    @6
    cC
    fveq1
    @60
    @16
    @25
    cG
    @6
    cC
    @11
    reseq1
    fveq2d
    eqeq12d
    ralbidv
    3anbi13d
    exbidv
    elabg
    syl
    mpbird
end
