include "cxp.mm"
include "cvv.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "co.mm"
include "c2nd.mm"
include "wceq.mm"
include "crio.mm"
include "wcel.mm"
include "xpexg.mm"
include "syl2anc.mm"
include "wa.mm"
include "wrex.mm"
include "simprr.mm"
include "simplr.mm"
include "weq.mm"
include "wb.mm"
include "an4s.mm"
include "anassrs.mm"
include "adantlrr.mm"
include "riota5.mm"
include "eqcomd.mm"
include "eqeq2.mm"
include "riotabidv.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "wn.mm"
include "wral.mm"
include "cdom.mm"
include "wbr.mm"
include "adantr.mm"
include "ad2antrr.mm"
include "wi.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "notbid.mm"
include "rspcv.mm"
include "adantl.mm"
include "cun.mm"
include "wo.mm"
include "3expa.mm"
include "elun.mm"
include "sylib.mm"
include "orcomd.mm"
include "ord.mm"
include "syld.mm"
include "impancom.mm"
include "ex.mm"
include "dom2d.mm"
include "mpd.mm"
include "mtand.mm"
include "dfrex2.mm"
include "sylibr.mm"
include "reximddv.mm"
include "cop.mm"
include "vex.mm"
include "op1std.mm"
include "oveq2d.mm"
include "op2ndd.mm"
include "eqeq12d.mm"
include "rexxp.mm"
include "wdomd.mm"

theorem unxpwdom3
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let cV: class V
  let cW: class W
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vx: setvar x
  let vy: setvar y
  assume unxpwdom3.av: |- ( ph -> A e. V )
  assume unxpwdom3.bv: |- ( ph -> B e. W )
  assume unxpwdom3.dv: |- ( ph -> D e. X )
  assume unxpwdom3.ov: |- ( ( ph /\ a e. C /\ b e. D ) -> ( a .+ b ) e. ( A u. B ) )
  assume unxpwdom3.lc: |- ( ( ( ph /\ a e. C ) /\ ( b e. D /\ c e. D ) ) -> ( ( a .+ b ) = ( a .+ c ) <-> b = c ) )
  assume unxpwdom3.rc: |- ( ( ( ph /\ d e. D ) /\ ( a e. C /\ c e. C ) ) -> ( ( c .+ d ) = ( a .+ d ) <-> c = a ) )
  assume unxpwdom3.ni: |- ( ph -> -. D ~<_ A )

  disjoint a b
  disjoint a c
  disjoint a d
  disjoint B a
  disjoint b c
  disjoint b d
  disjoint B b
  disjoint c d
  disjoint B c
  disjoint B d
  disjoint C a
  disjoint C b
  disjoint C c
  disjoint C d
  disjoint D a
  disjoint D b
  disjoint D c
  disjoint D d
  disjoint .+ a
  disjoint .+ b
  disjoint .+ c
  disjoint .+ d
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint d ph
  disjoint A b
  disjoint A c
  disjoint a x
  disjoint a y
  disjoint c x
  disjoint c y
  disjoint d x
  disjoint d y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  disjoint .+ x
  disjoint .+ y
  disjoint ph x
  assert |- ( ph -> C ~<_* ( D X. B ) )

  proof
    wph
    va
    vx
    cC
    cD
    cB
    cxp
    #
    cvv
    vc
    cv
    #
    vx
    cv
    #
    c1st
    cfv
    #
    c.pl
    co
    #
    @2
    c2nd
    cfv
    #
    wceq
    #
    vc
    cC
    crio
    #
    wph
    cD
    cX
    wcel
    cB
    cW
    wcel
    @0
    cvv
    wcel
    unxpwdom3.dv
    unxpwdom3.bv
    cD
    cB
    cX
    cW
    xpexg
    syl2anc
    wph
    va
    cv
    #
    cC
    wcel
    #
    wa
    #
    @8
    @1
    vd
    cv
    #
    c.pl
    co
    #
    vy
    cv
    #
    wceq
    #
    vc
    cC
    crio
    #
    wceq
    #
    vy
    cB
    wrex
    #
    vd
    cD
    wrex
    @8
    @7
    wceq
    #
    vx
    @0
    wrex
    @10
    @8
    @11
    c.pl
    co
    #
    cB
    wcel
    #
    @17
    vd
    cD
    @10
    @11
    cD
    wcel
    #
    @20
    wa
    #
    wa
    #
    @20
    @8
    @12
    @19
    wceq
    #
    vc
    cC
    crio
    #
    wceq
    #
    @17
    @10
    @21
    @20
    simprr
    @23
    @25
    @8
    @23
    @24
    vc
    cC
    @8
    wph
    @9
    @22
    simplr
    @10
    @21
    @1
    cC
    wcel
    #
    @24
    vc
    va
    weq
    wb
    #
    @20
    @10
    @21
    @27
    @28
    wph
    @21
    @9
    @27
    @28
    unxpwdom3.rc
    an4s
    anassrs
    adantlrr
    riota5
    eqcomd
    @16
    @26
    vy
    @19
    cB
    @13
    @19
    wceq
    #
    @15
    @25
    @8
    @29
    @14
    @24
    vc
    cC
    @13
    @19
    @12
    eqeq2
    riotabidv
    eqeq2d
    rspcev
    syl2anc
    @10
    @20
    wn
    #
    vd
    cD
    wral
    #
    wn
    @20
    vd
    cD
    wrex
    @10
    @31
    cD
    cA
    cdom
    wbr
    #
    wph
    @32
    wn
    @9
    unxpwdom3.ni
    adantr
    @10
    @31
    wa
    #
    cA
    cV
    wcel
    #
    @32
    wph
    @34
    @9
    @31
    unxpwdom3.av
    ad2antrr
    @33
    vb
    vc
    cD
    cA
    @8
    vb
    cv
    #
    c.pl
    co
    #
    @8
    @1
    c.pl
    co
    #
    cV
    @10
    @35
    cD
    wcel
    #
    @31
    @36
    cA
    wcel
    #
    @10
    @38
    wa
    #
    @31
    @36
    cB
    wcel
    #
    wn
    #
    @39
    @38
    @31
    @42
    wi
    @10
    @30
    @42
    vd
    @35
    cD
    vd
    vb
    weq
    #
    @20
    @41
    @43
    @19
    @36
    cB
    @11
    @35
    @8
    c.pl
    oveq2
    eleq1d
    notbid
    rspcv
    adantl
    @40
    @41
    @39
    @40
    @39
    @41
    @40
    @36
    cA
    cB
    cun
    wcel
    #
    @39
    @41
    wo
    wph
    @9
    @38
    @44
    unxpwdom3.ov
    3expa
    @36
    cA
    cB
    elun
    sylib
    orcomd
    ord
    syld
    impancom
    @10
    @38
    @1
    cD
    wcel
    wa
    #
    @36
    @37
    wceq
    vb
    vc
    weq
    wb
    #
    wi
    @31
    @10
    @45
    @46
    unxpwdom3.lc
    ex
    adantr
    dom2d
    mpd
    mtand
    @20
    vd
    cD
    dfrex2
    sylibr
    reximddv
    @18
    @16
    vx
    vd
    vy
    cD
    cB
    @2
    @11
    @13
    cop
    wceq
    #
    @7
    @15
    @8
    @47
    @6
    @14
    vc
    cC
    @47
    @4
    @12
    @5
    @13
    @47
    @3
    @11
    @1
    c.pl
    @11
    @13
    @2
    vd
    vex
    #
    vy
    vex
    #
    op1std
    oveq2d
    @11
    @13
    @2
    @48
    @49
    op2ndd
    eqeq12d
    riotabidv
    eqeq2d
    rexxp
    sylibr
    wdomd
end
