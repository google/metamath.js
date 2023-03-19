include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "cin.mm"
include "csn.mm"
include "wceq.mm"
include "co.mm"
include "wa.mm"
include "wrex.mm"
include "cabl.mm"
include "cgrp.mm"
include "ablgrp.mm"
include "subgid.mm"
include "3syl.mm"
include "cfn.mm"
include "wi.mm"
include "eleq1.mm"
include "eleq2.mm"
include "anbi12d.mm"
include "eqeq2.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "wpss.mm"
include "wal.mm"
include "wral.mm"
include "bi2.04.mm"
include "impexp.mm"
include "imbi2i.mm"
include "3bitr4i.mm"
include "albii.mm"
include "df-ral.mm"
include "r19.21v.mm"
include "3bitr2i.mm"
include "psseq1.mm"
include "ineq2.mm"
include "eqeq1d.mm"
include "oveq2.mm"
include "cbvrexv.mm"
include "syl5bb.mm"
include "cbvralv.mm"
include "cpgp.mm"
include "wbr.mm"
include "adantr.mm"
include "simprrl.mm"
include "simprrr.mm"
include "simprl.mm"
include "sylib.mm"
include "pgpfac1lem5.mm"
include "exp32.mm"
include "syl5bir.mm"
include "a2i.mm"
include "sylbi.mm"
include "a1i.mm"
include "findcard3.mm"
include "mpcom.mm"
include "mp2and.mm"

theorem pgpfac1
  let wph: wff ph
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cP: class P
  let c.po: class .(+)
  let cS: class S
  let cE: class E
  let cG: class G
  let cK: class K
  let cO: class O
  let c.0: class .0.
  let vb: setvar b
  let vk: setvar k
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let va: setvar a
  let vn: setvar n
  let cD: class D
  let cU: class U
  let cC: class C
  let cW: class W
  let c.x: class .x.
  assume pgpfac1.k: |- K = ( mrCls ` ( SubGrp ` G ) )
  assume pgpfac1.s: |- S = ( K ` { A } )
  assume pgpfac1.b: |- B = ( Base ` G )
  assume pgpfac1.o: |- O = ( od ` G )
  assume pgpfac1.e: |- E = ( gEx ` G )
  assume pgpfac1.z: |- .0. = ( 0g ` G )
  assume pgpfac1.l: |- .(+) = ( LSSum ` G )
  assume pgpfac1.p: |- ( ph -> P pGrp G )
  assume pgpfac1.g: |- ( ph -> G e. Abel )
  assume pgpfac1.n: |- ( ph -> B e. Fin )
  assume pgpfac1.oe: |- ( ph -> ( O ` A ) = E )
  assume pgpfac1.ab: |- ( ph -> A e. B )

  disjoint .0. t
  disjoint A t
  disjoint .(+) t
  disjoint P t
  disjoint B t
  disjoint G t
  disjoint S t
  disjoint ph t
  disjoint K t
  disjoint b k
  disjoint b s
  disjoint b t
  disjoint b u
  disjoint b v
  disjoint b x
  disjoint b y
  disjoint .0. b
  disjoint k s
  disjoint k t
  disjoint k u
  disjoint k v
  disjoint k x
  disjoint k y
  disjoint .0. k
  disjoint s t
  disjoint s u
  disjoint s v
  disjoint s x
  disjoint s y
  disjoint .0. s
  disjoint t u
  disjoint t v
  disjoint t x
  disjoint t y
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint .0. u
  disjoint v x
  disjoint v y
  disjoint .0. v
  disjoint x y
  disjoint .0. x
  disjoint .0. y
  disjoint b w
  disjoint A b
  disjoint k w
  disjoint A k
  disjoint s w
  disjoint A s
  disjoint t w
  disjoint u w
  disjoint A u
  disjoint v w
  disjoint A v
  disjoint w x
  disjoint w y
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint a b
  disjoint a n
  disjoint a t
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint D a
  disjoint b n
  disjoint D b
  disjoint n t
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint D n
  disjoint D t
  disjoint D w
  disjoint D x
  disjoint D y
  disjoint a k
  disjoint a s
  disjoint a u
  disjoint a v
  disjoint .(+) a
  disjoint .(+) b
  disjoint .(+) k
  disjoint .(+) s
  disjoint .(+) u
  disjoint .(+) v
  disjoint .(+) w
  disjoint .(+) x
  disjoint .(+) y
  disjoint E k
  disjoint O a
  disjoint P a
  disjoint P b
  disjoint P k
  disjoint P s
  disjoint P w
  disjoint P y
  disjoint B a
  disjoint k n
  disjoint B k
  disjoint n s
  disjoint n v
  disjoint B n
  disjoint B s
  disjoint B v
  disjoint G a
  disjoint G b
  disjoint G k
  disjoint n u
  disjoint G n
  disjoint G s
  disjoint G u
  disjoint G v
  disjoint G w
  disjoint G x
  disjoint G y
  disjoint U b
  disjoint U k
  disjoint U s
  disjoint U t
  disjoint U u
  disjoint U v
  disjoint U w
  disjoint U y
  disjoint C a
  disjoint C k
  disjoint C s
  disjoint C t
  disjoint C w
  disjoint S a
  disjoint S b
  disjoint S k
  disjoint S n
  disjoint S s
  disjoint S u
  disjoint S v
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint W a
  disjoint W b
  disjoint W k
  disjoint W n
  disjoint W s
  disjoint W t
  disjoint W w
  disjoint W x
  disjoint W y
  disjoint a ph
  disjoint b ph
  disjoint k ph
  disjoint n ph
  disjoint ph s
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint .x. a
  disjoint .x. b
  disjoint .x. k
  disjoint .x. n
  disjoint .x. s
  disjoint .x. t
  disjoint .x. w
  disjoint .x. y
  disjoint K s
  disjoint K w
  disjoint K x
  disjoint K y
  assert |- ( ph -> E. t e. ( SubGrp ` G ) ( ( S i^i t ) = { .0. } /\ ( S .(+) t ) = B ) )

  proof
    wph
    cB
    cG
    csubg
    cfv
    #
    wcel
    #
    cA
    cB
    wcel
    #
    cS
    vt
    cv
    #
    cin
    #
    c.0
    csn
    #
    wceq
    #
    cS
    @3
    c.po
    co
    #
    cB
    wceq
    #
    wa
    #
    vt
    @0
    wrex
    #
    wph
    cG
    cabl
    wcel
    #
    cG
    cgrp
    wcel
    @1
    pgpfac1.g
    cG
    ablgrp
    cB
    cG
    pgpfac1.b
    subgid
    3syl
    pgpfac1.ab
    cB
    cfn
    wcel
    #
    wph
    @1
    @2
    wa
    #
    @10
    wi
    #
    pgpfac1.n
    wph
    vs
    cv
    #
    @0
    wcel
    #
    cA
    @15
    wcel
    #
    wa
    #
    @6
    @7
    @15
    wceq
    #
    wa
    #
    vt
    @0
    wrex
    #
    wi
    #
    wi
    #
    wph
    vu
    cv
    #
    @0
    wcel
    #
    cA
    @24
    wcel
    #
    wa
    #
    @6
    @7
    @24
    wceq
    #
    wa
    #
    vt
    @0
    wrex
    #
    wi
    #
    wi
    #
    wph
    @14
    wi
    vs
    vu
    cB
    @15
    @24
    wceq
    #
    @22
    @31
    wph
    @33
    @18
    @27
    @21
    @30
    @33
    @16
    @25
    @17
    @26
    @15
    @24
    @0
    eleq1
    @15
    @24
    cA
    eleq2
    anbi12d
    @33
    @20
    @29
    vt
    @0
    @33
    @19
    @28
    @6
    @15
    @24
    @7
    eqeq2
    anbi2d
    rexbidv
    imbi12d
    imbi2d
    @15
    cB
    wceq
    #
    @22
    @14
    wph
    @34
    @18
    @13
    @21
    @10
    @34
    @16
    @1
    @17
    @2
    @15
    cB
    @0
    eleq1
    @15
    cB
    cA
    eleq2
    anbi12d
    @34
    @20
    @9
    vt
    @0
    @34
    @19
    @8
    @6
    @15
    cB
    @7
    eqeq2
    anbi2d
    rexbidv
    imbi12d
    imbi2d
    @15
    @24
    wpss
    #
    @23
    wi
    #
    vs
    wal
    #
    @32
    wi
    @24
    cfn
    wcel
    @37
    wph
    @35
    @17
    wa
    #
    @21
    wi
    #
    vs
    @0
    wral
    #
    wi
    #
    @32
    @37
    @16
    wph
    @39
    wi
    #
    wi
    #
    vs
    wal
    @42
    vs
    @0
    wral
    @41
    @36
    @43
    vs
    wph
    @35
    @22
    wi
    #
    wi
    wph
    @16
    @39
    wi
    #
    wi
    @36
    @43
    @44
    @45
    wph
    @35
    @16
    @17
    @21
    wi
    #
    wi
    #
    wi
    @16
    @35
    @46
    wi
    #
    wi
    @44
    @45
    @35
    @16
    @46
    bi2.04
    @22
    @47
    @35
    @16
    @17
    @21
    impexp
    imbi2i
    @39
    @48
    @16
    @35
    @17
    @21
    impexp
    imbi2i
    3bitr4i
    imbi2i
    @35
    wph
    @22
    bi2.04
    @16
    wph
    @39
    bi2.04
    3bitr4i
    albii
    @42
    vs
    @0
    df-ral
    wph
    @39
    vs
    @0
    r19.21v
    3bitr2i
    wph
    @40
    @31
    @40
    vx
    cv
    #
    @24
    wpss
    #
    cA
    @49
    wcel
    #
    wa
    #
    cS
    vy
    cv
    #
    cin
    #
    @5
    wceq
    #
    cS
    @53
    c.po
    co
    #
    @49
    wceq
    #
    wa
    #
    vy
    @0
    wrex
    #
    wi
    #
    vx
    @0
    wral
    #
    wph
    @31
    @60
    @39
    vx
    vs
    @0
    @49
    @15
    wceq
    #
    @52
    @38
    @59
    @21
    @62
    @50
    @35
    @51
    @17
    @49
    @15
    @24
    psseq1
    @49
    @15
    cA
    eleq2
    anbi12d
    @59
    @6
    @7
    @49
    wceq
    #
    wa
    #
    vt
    @0
    wrex
    @62
    @21
    @58
    @64
    vy
    vt
    @0
    @53
    @3
    wceq
    #
    @55
    @6
    @57
    @63
    @65
    @54
    @4
    @5
    @53
    @3
    cS
    ineq2
    eqeq1d
    @65
    @56
    @7
    @49
    @53
    @3
    cS
    c.po
    oveq2
    eqeq1d
    anbi12d
    cbvrexv
    @62
    @64
    @20
    vt
    @0
    @62
    @63
    @19
    @6
    @49
    @15
    @7
    eqeq2
    anbi2d
    rexbidv
    syl5bb
    imbi12d
    cbvralv
    #
    wph
    @61
    @27
    @30
    wph
    @61
    @27
    wa
    #
    wa
    #
    vt
    cA
    cB
    cP
    c.po
    cS
    @24
    cE
    cG
    cK
    cO
    c.0
    vs
    pgpfac1.k
    pgpfac1.s
    pgpfac1.b
    pgpfac1.o
    pgpfac1.e
    pgpfac1.z
    pgpfac1.l
    wph
    cP
    cG
    cpgp
    wbr
    @67
    pgpfac1.p
    adantr
    wph
    @11
    @67
    pgpfac1.g
    adantr
    wph
    @12
    @67
    pgpfac1.n
    adantr
    wph
    cA
    cO
    cfv
    cE
    wceq
    @67
    pgpfac1.oe
    adantr
    wph
    @61
    @25
    @26
    simprrl
    wph
    @61
    @25
    @26
    simprrr
    @68
    @61
    @40
    wph
    @61
    @27
    simprl
    @66
    sylib
    pgpfac1lem5
    exp32
    syl5bir
    a2i
    sylbi
    a1i
    findcard3
    mpcom
    mp2and
end
