include "comi.mm"
include "co.mm"
include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cop.mm"
include "cplusg.mm"
include "cts.mm"
include "ctp.mm"
include "ctop.mm"
include "cv.mm"
include "cuni.mm"
include "cc0.mm"
include "wceq.mm"
include "c1.mm"
include "wa.mm"
include "cii.mm"
include "ccn.mm"
include "crab.mm"
include "cpco.mm"
include "cxko.mm"
include "cvv.mm"
include "cmpt2.mm"
include "df-om1.mm"
include "a1i.mm"
include "simprl.mm"
include "oveq2d.mm"
include "simprr.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "rabeqbidv.mm"
include "adantr.mm"
include "eqtr4d.mm"
include "opeq2d.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "tpeq123d.mm"
include "unieq.mm"
include "adantl.mm"
include "ctopon.mm"
include "wcel.mm"
include "toponuni.mm"
include "syl.mm"
include "topontop.mm"
include "tpex.mm"
include "ovmpt2dx.mm"
include "syl5eq.mm"

theorem om1val
  let wph: wff ph
  let cB: class B
  let c.pl: class .+
  let vf: setvar f
  let cJ: class J
  let cK: class K
  let cO: class O
  let cX: class X
  let cY: class Y
  let vj: setvar j
  let vy: setvar y
  assume om1val.o: |- O = ( J Om1 Y )
  assume om1val.b: |- ( ph -> B = { f e. ( II Cn J ) | ( ( f ` 0 ) = Y /\ ( f ` 1 ) = Y ) } )
  assume om1val.p: |- ( ph -> .+ = ( *p ` J ) )
  assume om1val.k: |- ( ph -> K = ( J ^ko II ) )
  assume om1val.j: |- ( ph -> J e. ( TopOn ` X ) )
  assume om1val.y: |- ( ph -> Y e. X )

  disjoint J f
  disjoint f ph
  disjoint Y f
  disjoint j y
  disjoint B j
  disjoint B y
  disjoint f j
  disjoint f y
  disjoint J j
  disjoint J y
  disjoint j ph
  disjoint ph y
  disjoint Y j
  disjoint Y y
  disjoint K j
  disjoint K y
  disjoint .+ j
  disjoint .+ y
  assert |- ( ph -> O = { <. ( Base ` ndx ) , B >. , <. ( +g ` ndx ) , .+ >. , <. ( TopSet ` ndx ) , K >. } )

  proof
    wph
    cO
    cJ
    cY
    comi
    co
    cnx
    cbs
    cfv
    #
    cB
    cop
    #
    cnx
    cplusg
    cfv
    #
    c.pl
    cop
    #
    cnx
    cts
    cfv
    #
    cK
    cop
    #
    ctp
    #
    om1val.o
    wph
    vj
    vy
    cJ
    cY
    ctop
    vj
    cv
    #
    cuni
    #
    @0
    cc0
    vf
    cv
    #
    cfv
    #
    vy
    cv
    #
    wceq
    #
    c1
    @9
    cfv
    #
    @11
    wceq
    #
    wa
    #
    vf
    cii
    @7
    ccn
    co
    #
    crab
    #
    cop
    #
    @2
    @7
    cpco
    cfv
    #
    cop
    #
    @4
    @7
    cii
    cxko
    co
    #
    cop
    #
    ctp
    #
    @6
    comi
    cX
    cvv
    comi
    vj
    vy
    ctop
    @8
    @23
    cmpt2
    wceq
    wph
    vy
    vf
    vj
    df-om1
    a1i
    wph
    @7
    cJ
    wceq
    #
    @11
    cY
    wceq
    #
    wa
    #
    wa
    #
    @18
    @1
    @20
    @3
    @22
    @5
    @27
    @17
    cB
    @0
    @27
    @17
    @10
    cY
    wceq
    #
    @13
    cY
    wceq
    #
    wa
    #
    vf
    cii
    cJ
    ccn
    co
    #
    crab
    #
    cB
    @27
    @15
    @30
    vf
    @16
    @31
    @27
    @7
    cJ
    cii
    ccn
    wph
    @24
    @25
    simprl
    #
    oveq2d
    @27
    @12
    @28
    @14
    @29
    @27
    @11
    cY
    @10
    wph
    @24
    @25
    simprr
    #
    eqeq2d
    @27
    @11
    cY
    @13
    @34
    eqeq2d
    anbi12d
    rabeqbidv
    wph
    cB
    @32
    wceq
    @26
    om1val.b
    adantr
    eqtr4d
    opeq2d
    @27
    @19
    c.pl
    @2
    @27
    @19
    cJ
    cpco
    cfv
    #
    c.pl
    @27
    @7
    cJ
    cpco
    @33
    fveq2d
    wph
    c.pl
    @35
    wceq
    @26
    om1val.p
    adantr
    eqtr4d
    opeq2d
    @27
    @21
    cK
    @4
    @27
    @21
    cJ
    cii
    cxko
    co
    #
    cK
    @27
    @7
    cJ
    cii
    cxko
    @33
    oveq1d
    wph
    cK
    @36
    wceq
    @26
    om1val.k
    adantr
    eqtr4d
    opeq2d
    tpeq123d
    wph
    @24
    wa
    @8
    cJ
    cuni
    #
    cX
    @24
    @8
    @37
    wceq
    wph
    @7
    cJ
    unieq
    adantl
    wph
    cX
    @37
    wceq
    #
    @24
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    @38
    om1val.j
    cX
    cJ
    toponuni
    syl
    adantr
    eqtr4d
    wph
    @39
    cJ
    ctop
    wcel
    om1val.j
    cX
    cJ
    topontop
    syl
    om1val.y
    @6
    cvv
    wcel
    wph
    @1
    @3
    @5
    tpex
    a1i
    ovmpt2dx
    syl5eq
end
