include "cdif.mm"
include "c0.mm"
include "wceq.mm"
include "cc0.mm"
include "cv.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "wa.mm"
include "wral.mm"
include "clt.mm"
include "w3a.mm"
include "wrex.mm"
include "cmpt.mm"
include "wcel.mm"
include "cr.mm"
include "0re.mm"
include "stoweidlem4.mm"
include "mpan2.mm"
include "adantr.mm"
include "nfcv.mm"
include "nfdif.mm"
include "nfeq.mm"
include "nfan.mm"
include "0le0.mm"
include "cc.mm"
include "0cn.mm"
include "eqid.mm"
include "fvmpt2.mm"
include "syl5breqr.mm"
include "adantl.mm"
include "0le1.mm"
include "syl6eqbr.mm"
include "jca.mm"
include "ex.mm"
include "ralrimi.mm"
include "cuni.mm"
include "elunii.mm"
include "syl6eleqr.mm"
include "eqidd.mm"
include "c0ex.mm"
include "fvmpt.mm"
include "3syl.mm"
include "rzalf.mm"
include "nfmpt1.mm"
include "fveq1.mm"
include "breq2d.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "ralbid.mm"
include "eqeq1d.mm"
include "3anbi123d.mm"
include "rspcev.mm"
include "syl13anc.mm"
include "wn.mm"
include "nfn.mm"
include "ccmp.mm"
include "wss.mm"
include "caddc.mm"
include "co.mm"
include "3adant1r.mm"
include "cmul.mm"
include "adantlr.mm"
include "wne.mm"
include "neqne.mm"
include "stoweidlem53.mm"
include "pm2.61dan.mm"

theorem stoweidlem55
  let wph: wff ph
  let vx: setvar x
  let vw: setvar w
  let vt: setvar t
  let cA: class A
  let cC: class C
  let cQ: class Q
  let cT: class T
  let cU: class U
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let cJ: class J
  let cK: class K
  let cW: class W
  let cZ: class Z
  let vr: setvar r
  let vq: setvar q
  let vp: setvar p
  let vk: setvar k
  assume stoweidlem55.1: |- F/_ t U
  assume stoweidlem55.2: |- F/ t ph
  assume stoweidlem55.3: |- K = ( topGen ` ran (,) )
  assume stoweidlem55.4: |- ( ph -> J e. Comp )
  assume stoweidlem55.5: |- T = U. J
  assume stoweidlem55.6: |- C = ( J Cn K )
  assume stoweidlem55.7: |- ( ph -> A C_ C )
  assume stoweidlem55.8: |- ( ( ph /\ f e. A /\ g e. A ) -> ( t e. T |-> ( ( f ` t ) + ( g ` t ) ) ) e. A )
  assume stoweidlem55.9: |- ( ( ph /\ f e. A /\ g e. A ) -> ( t e. T |-> ( ( f ` t ) x. ( g ` t ) ) ) e. A )
  assume stoweidlem55.10: |- ( ( ph /\ x e. RR ) -> ( t e. T |-> x ) e. A )
  assume stoweidlem55.11: |- ( ( ph /\ ( r e. T /\ t e. T /\ r =/= t ) ) -> E. q e. A ( q ` r ) =/= ( q ` t ) )
  assume stoweidlem55.12: |- ( ph -> U e. J )
  assume stoweidlem55.13: |- ( ph -> Z e. U )
  assume stoweidlem55.14: |- Q = { h e. A | ( ( h ` Z ) = 0 /\ A. t e. T ( 0 <_ ( h ` t ) /\ ( h ` t ) <_ 1 ) ) }
  assume stoweidlem55.15: |- W = { w e. J | E. h e. Q w = { t e. T | 0 < ( h ` t ) } }

  disjoint f g
  disjoint f h
  disjoint f q
  disjoint f t
  disjoint T f
  disjoint g h
  disjoint g q
  disjoint g t
  disjoint T g
  disjoint h q
  disjoint h t
  disjoint T h
  disjoint q t
  disjoint T q
  disjoint T t
  disjoint f r
  disjoint A f
  disjoint g r
  disjoint A g
  disjoint q r
  disjoint A q
  disjoint r t
  disjoint A r
  disjoint A t
  disjoint f x
  disjoint h x
  disjoint q x
  disjoint t x
  disjoint T x
  disjoint Q f
  disjoint Q g
  disjoint Q q
  disjoint U f
  disjoint U g
  disjoint U h
  disjoint U q
  disjoint Z f
  disjoint Z g
  disjoint Z h
  disjoint Z q
  disjoint Z t
  disjoint f ph
  disjoint g ph
  disjoint h ph
  disjoint ph q
  disjoint g w
  disjoint h w
  disjoint t w
  disjoint T w
  disjoint W g
  disjoint A h
  disjoint A x
  disjoint J h
  disjoint J t
  disjoint J w
  disjoint p q
  disjoint p t
  disjoint T p
  disjoint A p
  disjoint U p
  disjoint Z p
  disjoint r x
  disjoint T r
  disjoint U r
  disjoint U x
  disjoint ph r
  disjoint ph x
  disjoint K t
  disjoint w x
  disjoint Q w
  disjoint Q x
  disjoint U w
  disjoint ph w
  disjoint Z x
  disjoint k x
  assert |- ( ph -> E. p e. A ( A. t e. T ( 0 <_ ( p ` t ) /\ ( p ` t ) <_ 1 ) /\ ( p ` Z ) = 0 /\ A. t e. ( T \ U ) 0 < ( p ` t ) ) )

  proof
    wph
    cT
    cU
    cdif
    #
    c0
    wceq
    #
    cc0
    vt
    cv
    #
    vp
    cv
    #
    cfv
    #
    cle
    wbr
    #
    @4
    c1
    cle
    wbr
    #
    wa
    #
    vt
    cT
    wral
    #
    cZ
    @3
    cfv
    #
    cc0
    wceq
    #
    cc0
    @4
    clt
    wbr
    #
    vt
    @0
    wral
    #
    w3a
    #
    vp
    cA
    wrex
    #
    wph
    @1
    wa
    #
    vt
    cT
    cc0
    cmpt
    #
    cA
    wcel
    #
    cc0
    @2
    @16
    cfv
    #
    cle
    wbr
    #
    @18
    c1
    cle
    wbr
    #
    wa
    #
    vt
    cT
    wral
    #
    cZ
    @16
    cfv
    #
    cc0
    wceq
    #
    cc0
    @18
    clt
    wbr
    #
    vt
    @0
    wral
    #
    @14
    wph
    @17
    @1
    wph
    cc0
    cr
    wcel
    @17
    0re
    wph
    vx
    vt
    cA
    cc0
    cT
    stoweidlem55.10
    stoweidlem4
    mpan2
    adantr
    @15
    @21
    vt
    cT
    wph
    @1
    vt
    stoweidlem55.2
    vt
    @0
    c0
    vt
    cT
    cU
    vt
    cT
    nfcv
    stoweidlem55.1
    nfdif
    vt
    c0
    nfcv
    nfeq
    #
    nfan
    @15
    @2
    cT
    wcel
    #
    @21
    @15
    @28
    wa
    @19
    @20
    @28
    @19
    @15
    @28
    cc0
    cc0
    @18
    cle
    0le0
    @28
    cc0
    cc
    wcel
    @18
    cc0
    wceq
    0cn
    vt
    cT
    cc0
    cc
    @16
    @16
    eqid
    #
    fvmpt2
    mpan2
    #
    syl5breqr
    adantl
    @28
    @20
    @15
    @28
    @18
    cc0
    c1
    cle
    @30
    0le1
    syl6eqbr
    adantl
    jca
    ex
    ralrimi
    wph
    @24
    @1
    wph
    cZ
    cU
    wcel
    #
    cU
    cJ
    wcel
    #
    wa
    #
    cZ
    cT
    wcel
    @24
    wph
    @31
    @32
    stoweidlem55.13
    stoweidlem55.12
    jca
    @33
    cZ
    cJ
    cuni
    cT
    cZ
    cU
    cJ
    elunii
    stoweidlem55.5
    syl6eleqr
    vt
    cZ
    cc0
    cc0
    cT
    @16
    @2
    cZ
    wceq
    cc0
    eqidd
    @29
    c0ex
    fvmpt
    3syl
    adantr
    @1
    @26
    wph
    @25
    vt
    @0
    @27
    rzalf
    adantl
    @13
    @22
    @24
    @26
    w3a
    vp
    @16
    cA
    @3
    @16
    wceq
    #
    @8
    @22
    @10
    @24
    @12
    @26
    @34
    @7
    @21
    vt
    cT
    vt
    @3
    @16
    vt
    @3
    nfcv
    vt
    cT
    cc0
    nfmpt1
    nfeq
    #
    @34
    @5
    @19
    @6
    @20
    @34
    @4
    @18
    cc0
    cle
    @2
    @3
    @16
    fveq1
    #
    breq2d
    @34
    @4
    @18
    c1
    cle
    @36
    breq1d
    anbi12d
    ralbid
    @34
    @9
    @23
    cc0
    cZ
    @3
    @16
    fveq1
    eqeq1d
    @34
    @11
    @25
    vt
    @0
    @35
    @34
    @4
    @18
    cc0
    clt
    @36
    breq2d
    ralbid
    3anbi123d
    rspcev
    syl13anc
    wph
    @1
    wn
    #
    wa
    vx
    vw
    vt
    cA
    cC
    cQ
    cT
    cU
    vf
    vg
    vh
    cJ
    cK
    cW
    cZ
    vr
    vq
    vp
    stoweidlem55.1
    wph
    @37
    vt
    stoweidlem55.2
    @1
    vt
    @27
    nfn
    nfan
    stoweidlem55.3
    stoweidlem55.14
    stoweidlem55.15
    stoweidlem55.5
    stoweidlem55.6
    wph
    cJ
    ccmp
    wcel
    @37
    stoweidlem55.4
    adantr
    wph
    cA
    cC
    wss
    @37
    stoweidlem55.7
    adantr
    wph
    vf
    cv
    #
    cA
    wcel
    #
    vg
    cv
    #
    cA
    wcel
    #
    vt
    cT
    @2
    @38
    cfv
    #
    @2
    @40
    cfv
    #
    caddc
    co
    cmpt
    cA
    wcel
    @37
    stoweidlem55.8
    3adant1r
    wph
    @39
    @41
    vt
    cT
    @42
    @43
    cmul
    co
    cmpt
    cA
    wcel
    @37
    stoweidlem55.9
    3adant1r
    wph
    vx
    cv
    #
    cr
    wcel
    vt
    cT
    @44
    cmpt
    cA
    wcel
    @37
    stoweidlem55.10
    adantlr
    wph
    vr
    cv
    #
    cT
    wcel
    @28
    @45
    @2
    wne
    w3a
    @45
    vq
    cv
    #
    cfv
    @2
    @46
    cfv
    wne
    vq
    cA
    wrex
    @37
    stoweidlem55.11
    adantlr
    wph
    @32
    @37
    stoweidlem55.12
    adantr
    @37
    @0
    c0
    wne
    wph
    @0
    c0
    neqne
    adantl
    wph
    @31
    @37
    stoweidlem55.13
    adantr
    stoweidlem53
    pm2.61dan
end
