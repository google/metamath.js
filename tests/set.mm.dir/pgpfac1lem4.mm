include "co.mm"
include "cv.mm"
include "cplusg.mm"
include "cfv.mm"
include "wcel.mm"
include "cin.mm"
include "csn.mm"
include "wceq.mm"
include "wa.mm"
include "csubg.mm"
include "wrex.mm"
include "cz.mm"
include "csg.mm"
include "pgpfac1lem2.mm"
include "cabl.mm"
include "cmre.mm"
include "cgrp.mm"
include "cacs.mm"
include "ablgrp.mm"
include "syl.mm"
include "subgacs.mm"
include "acsmre.mm"
include "3syl.mm"
include "wss.mm"
include "subgss.mm"
include "sseldd.mm"
include "mrcsncl.mm"
include "syl2anc.mm"
include "syl5eqel.mm"
include "lsmcom.mm"
include "syl3anc.mm"
include "eleqtrd.mm"
include "eqid.mm"
include "lsmelvalm.mm"
include "mpbid.mm"
include "cmpt.mm"
include "crn.mm"
include "cycsubg2.mm"
include "syl5eq.mm"
include "rexeqdv.mm"
include "cvv.mm"
include "wral.mm"
include "wb.mm"
include "ovex.mm"
include "rgenw.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "rexrnmpt.mm"
include "ax-mp.mm"
include "syl6bb.mm"
include "rexbidv.mm"
include "rexcom.mm"
include "sylib.mm"
include "ad2antrr.mm"
include "adantr.mm"
include "sselda.mm"
include "simplr.mm"
include "mulgcl.mm"
include "cpgp.mm"
include "wbr.mm"
include "cprime.mm"
include "pgpprm.mm"
include "prmz.mm"
include "eldifad.mm"
include "grpsubadd.mm"
include "syl13anc.mm"
include "eqcom.mm"
include "3bitr4g.mm"
include "rexbidva.mm"
include "risset.mm"
include "syl6bbr.mm"
include "cdiv.mm"
include "cfn.mm"
include "wpss.mm"
include "wn.mm"
include "wi.mm"
include "cdif.mm"
include "simprl.mm"
include "simprr.mm"
include "pgpfac1lem3.mm"
include "rexlimddv.mm"

theorem pgpfac1lem4
  let wph: wff ph
  let vw: setvar w
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let c.po: class .(+)
  let cS: class S
  let c.x: class .x.
  let cU: class U
  let cE: class E
  let cG: class G
  let cK: class K
  let cO: class O
  let cW: class W
  let c.0: class .0.
  let vb: setvar b
  let vk: setvar k
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let va: setvar a
  let vn: setvar n
  let cD: class D
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
  assume pgpfac1.u: |- ( ph -> U e. ( SubGrp ` G ) )
  assume pgpfac1.au: |- ( ph -> A e. U )
  assume pgpfac1.w: |- ( ph -> W e. ( SubGrp ` G ) )
  assume pgpfac1.i: |- ( ph -> ( S i^i W ) = { .0. } )
  assume pgpfac1.ss: |- ( ph -> ( S .(+) W ) C_ U )
  assume pgpfac1.2: |- ( ph -> A. w e. ( SubGrp ` G ) ( ( w C. U /\ A e. w ) -> -. ( S .(+) W ) C. w ) )
  assume pgpfac1.c: |- ( ph -> C e. ( U \ ( S .(+) W ) ) )
  assume pgpfac1.mg: |- .x. = ( .g ` G )

  disjoint .0. t
  disjoint t w
  disjoint A t
  disjoint A w
  disjoint .(+) t
  disjoint .(+) w
  disjoint P t
  disjoint P w
  disjoint B t
  disjoint G t
  disjoint G w
  disjoint U t
  disjoint U w
  disjoint C t
  disjoint C w
  disjoint S t
  disjoint S w
  disjoint W t
  disjoint W w
  disjoint ph t
  disjoint ph w
  disjoint .x. t
  disjoint .x. w
  disjoint K t
  disjoint K w
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
  disjoint u w
  disjoint A u
  disjoint v w
  disjoint A v
  disjoint w x
  disjoint w y
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
  disjoint .(+) x
  disjoint .(+) y
  disjoint E k
  disjoint O a
  disjoint P a
  disjoint P b
  disjoint P k
  disjoint P s
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
  disjoint G x
  disjoint G y
  disjoint U b
  disjoint U k
  disjoint U s
  disjoint U u
  disjoint U v
  disjoint U y
  disjoint C a
  disjoint C k
  disjoint C s
  disjoint S a
  disjoint S b
  disjoint S k
  disjoint S n
  disjoint S s
  disjoint S u
  disjoint S v
  disjoint S x
  disjoint S y
  disjoint W a
  disjoint W b
  disjoint W k
  disjoint W n
  disjoint W s
  disjoint W x
  disjoint W y
  disjoint a ph
  disjoint b ph
  disjoint k ph
  disjoint n ph
  disjoint ph s
  disjoint ph u
  disjoint ph v
  disjoint ph x
  disjoint ph y
  disjoint .x. a
  disjoint .x. b
  disjoint .x. k
  disjoint .x. n
  disjoint .x. s
  disjoint .x. y
  disjoint K s
  disjoint K x
  disjoint K y
  assert |- ( ph -> E. t e. ( SubGrp ` G ) ( ( S i^i t ) = { .0. } /\ ( S .(+) t ) = U ) )

  proof
    wph
    cP
    cC
    c.x
    co
    #
    vk
    cv
    #
    cA
    c.x
    co
    #
    cG
    cplusg
    cfv
    #
    co
    #
    cW
    wcel
    #
    cS
    vt
    cv
    #
    cin
    c.0
    csn
    #
    wceq
    cS
    @6
    c.po
    co
    cU
    wceq
    wa
    vt
    cG
    csubg
    cfv
    #
    wrex
    vk
    cz
    wph
    @0
    vw
    cv
    #
    @2
    cG
    csg
    cfv
    #
    co
    #
    wceq
    #
    vw
    cW
    wrex
    #
    vk
    cz
    wrex
    #
    @5
    vk
    cz
    wrex
    wph
    @12
    vk
    cz
    wrex
    #
    vw
    cW
    wrex
    #
    @14
    wph
    @0
    @9
    vs
    cv
    #
    @10
    co
    #
    wceq
    #
    vs
    cS
    wrex
    #
    vw
    cW
    wrex
    #
    @16
    wph
    @0
    cW
    cS
    c.po
    co
    #
    wcel
    @21
    wph
    @0
    cS
    cW
    c.po
    co
    #
    @22
    wph
    vw
    cA
    cB
    cC
    cP
    c.po
    cS
    c.x
    cU
    cE
    cG
    cK
    cO
    cW
    c.0
    pgpfac1.k
    pgpfac1.s
    pgpfac1.b
    pgpfac1.o
    pgpfac1.e
    pgpfac1.z
    pgpfac1.l
    pgpfac1.p
    pgpfac1.g
    pgpfac1.n
    pgpfac1.oe
    pgpfac1.u
    pgpfac1.au
    pgpfac1.w
    pgpfac1.i
    pgpfac1.ss
    pgpfac1.2
    pgpfac1.c
    pgpfac1.mg
    pgpfac1lem2
    wph
    cG
    cabl
    wcel
    #
    cS
    @8
    wcel
    cW
    @8
    wcel
    #
    @23
    @22
    wceq
    pgpfac1.g
    wph
    cS
    cA
    csn
    cK
    cfv
    #
    @8
    pgpfac1.s
    wph
    @8
    cB
    cmre
    cfv
    wcel
    #
    cA
    cB
    wcel
    #
    @26
    @8
    wcel
    wph
    cG
    cgrp
    wcel
    #
    @8
    cB
    cacs
    cfv
    wcel
    @27
    wph
    @24
    @29
    pgpfac1.g
    cG
    ablgrp
    syl
    #
    cB
    cG
    pgpfac1.b
    subgacs
    @8
    cB
    acsmre
    3syl
    wph
    cU
    cB
    cA
    wph
    cU
    @8
    wcel
    #
    cU
    cB
    wss
    pgpfac1.u
    cB
    cU
    cG
    pgpfac1.b
    subgss
    syl
    #
    pgpfac1.au
    sseldd
    #
    @8
    cA
    cK
    cB
    pgpfac1.k
    mrcsncl
    syl2anc
    syl5eqel
    #
    pgpfac1.w
    c.po
    cS
    cW
    cG
    pgpfac1.l
    lsmcom
    syl3anc
    eleqtrd
    wph
    vw
    vs
    c.po
    cW
    cS
    cG
    @10
    @0
    @10
    eqid
    #
    pgpfac1.l
    pgpfac1.w
    @34
    lsmelvalm
    mpbid
    wph
    @20
    @15
    vw
    cW
    wph
    @20
    @19
    vs
    vk
    cz
    @2
    cmpt
    #
    crn
    #
    wrex
    #
    @15
    wph
    @19
    vs
    cS
    @37
    wph
    cS
    @26
    @37
    pgpfac1.s
    wph
    @29
    @28
    @26
    @37
    wceq
    @30
    @33
    vk
    cA
    c.x
    @36
    cG
    cK
    cB
    pgpfac1.b
    pgpfac1.mg
    @36
    eqid
    #
    pgpfac1.k
    cycsubg2
    syl2anc
    syl5eq
    rexeqdv
    @2
    cvv
    wcel
    #
    vk
    cz
    wral
    @38
    @15
    wb
    @40
    vk
    cz
    @1
    cA
    c.x
    ovex
    rgenw
    @19
    @12
    vk
    vs
    cz
    @2
    @36
    cvv
    @39
    @17
    @2
    wceq
    @18
    @11
    @0
    @17
    @2
    @9
    @10
    oveq2
    eqeq2d
    rexrnmpt
    ax-mp
    syl6bb
    rexbidv
    mpbid
    @12
    vw
    vk
    cW
    cz
    rexcom
    sylib
    wph
    @13
    @5
    vk
    cz
    wph
    @1
    cz
    wcel
    #
    wa
    #
    @13
    @9
    @4
    wceq
    #
    vw
    cW
    wrex
    @5
    @42
    @12
    @43
    vw
    cW
    @42
    @9
    cW
    wcel
    #
    wa
    #
    @11
    @0
    wceq
    #
    @4
    @9
    wceq
    #
    @12
    @43
    @45
    @29
    @9
    cB
    wcel
    @2
    cB
    wcel
    #
    @0
    cB
    wcel
    #
    @46
    @47
    wb
    wph
    @29
    @41
    @44
    @30
    ad2antrr
    #
    @42
    cW
    cB
    @9
    wph
    cW
    cB
    wss
    #
    @41
    wph
    @25
    @51
    pgpfac1.w
    cB
    cW
    cG
    pgpfac1.b
    subgss
    syl
    adantr
    sselda
    @45
    @29
    @41
    @28
    @48
    @50
    wph
    @41
    @44
    simplr
    wph
    @28
    @41
    @44
    @33
    ad2antrr
    cB
    c.x
    cG
    @1
    cA
    pgpfac1.b
    pgpfac1.mg
    mulgcl
    syl3anc
    wph
    @49
    @41
    @44
    wph
    @29
    cP
    cz
    wcel
    #
    cC
    cB
    wcel
    @49
    @30
    wph
    cP
    cG
    cpgp
    wbr
    #
    cP
    cprime
    wcel
    @52
    pgpfac1.p
    cP
    cG
    pgpprm
    cP
    prmz
    3syl
    wph
    cU
    cB
    cC
    @32
    wph
    cC
    cU
    @23
    pgpfac1.c
    eldifad
    sseldd
    cB
    c.x
    cG
    cP
    cC
    pgpfac1.b
    pgpfac1.mg
    mulgcl
    syl3anc
    ad2antrr
    cB
    @3
    cG
    @10
    @9
    @2
    @0
    pgpfac1.b
    @3
    eqid
    @35
    grpsubadd
    syl13anc
    @0
    @11
    eqcom
    @9
    @4
    eqcom
    3bitr4g
    rexbidva
    vw
    @4
    cW
    risset
    syl6bbr
    rexbidva
    mpbid
    wph
    @41
    @5
    wa
    #
    wa
    vw
    vt
    cA
    cB
    cC
    cC
    @1
    cP
    cdiv
    co
    cA
    c.x
    co
    @3
    co
    #
    cP
    c.po
    cS
    c.x
    cU
    cE
    cG
    cK
    @1
    cO
    cW
    c.0
    pgpfac1.k
    pgpfac1.s
    pgpfac1.b
    pgpfac1.o
    pgpfac1.e
    pgpfac1.z
    pgpfac1.l
    wph
    @53
    @54
    pgpfac1.p
    adantr
    wph
    @24
    @54
    pgpfac1.g
    adantr
    wph
    cB
    cfn
    wcel
    @54
    pgpfac1.n
    adantr
    wph
    cA
    cO
    cfv
    cE
    wceq
    @54
    pgpfac1.oe
    adantr
    wph
    @31
    @54
    pgpfac1.u
    adantr
    wph
    cA
    cU
    wcel
    @54
    pgpfac1.au
    adantr
    wph
    @25
    @54
    pgpfac1.w
    adantr
    wph
    cS
    cW
    cin
    @7
    wceq
    @54
    pgpfac1.i
    adantr
    wph
    @23
    cU
    wss
    @54
    pgpfac1.ss
    adantr
    wph
    @9
    cU
    wpss
    cA
    @9
    wcel
    wa
    @23
    @9
    wpss
    wn
    wi
    vw
    @8
    wral
    @54
    pgpfac1.2
    adantr
    wph
    cC
    cU
    @23
    cdif
    wcel
    @54
    pgpfac1.c
    adantr
    pgpfac1.mg
    wph
    @41
    @5
    simprl
    wph
    @41
    @5
    simprr
    @55
    eqid
    pgpfac1lem3
    rexlimddv
end
