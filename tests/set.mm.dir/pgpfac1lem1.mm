include "co.mm"
include "cdif.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cfv.mm"
include "wss.mm"
include "wceq.mm"
include "adantr.mm"
include "csubg.mm"
include "cmre.mm"
include "cabl.mm"
include "cgrp.mm"
include "cacs.mm"
include "ablgrp.mm"
include "subgacs.mm"
include "acsmre.mm"
include "4syl.mm"
include "eldifi.mm"
include "adantl.mm"
include "snssd.mm"
include "mrcsscl.mm"
include "syl3anc.mm"
include "wb.mm"
include "subgss.mm"
include "syl.mm"
include "sseldd.mm"
include "mrcsncl.mm"
include "syl2anc.mm"
include "syl5eqel.mm"
include "lsmsubg2.mm"
include "sselda.mm"
include "sylan2.mm"
include "lsmlub.mm"
include "mpbi2and.mm"
include "wpss.mm"
include "wn.mm"
include "wi.mm"
include "lsmub1.mm"
include "lsmub2.mm"
include "mrcssidd.mm"
include "snssg.mm"
include "mpbird.mm"
include "eldifn.mm"
include "ssnelpssd.mm"
include "syl6sseqr.mm"
include "cv.mm"
include "wral.mm"
include "psseq1.mm"
include "eleq2.mm"
include "anbi12d.mm"
include "psseq2.mm"
include "notbid.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "sylc.mm"
include "mpan2d.mm"
include "mt2d.mm"
include "npss.mm"
include "sylib.mm"
include "mpd.mm"

theorem pgpfac1lem1
  let wph: wff ph
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let c.po: class .(+)
  let cS: class S
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
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let va: setvar a
  let vn: setvar n
  let cD: class D
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
  assume pgpfac1.u: |- ( ph -> U e. ( SubGrp ` G ) )
  assume pgpfac1.au: |- ( ph -> A e. U )
  assume pgpfac1.w: |- ( ph -> W e. ( SubGrp ` G ) )
  assume pgpfac1.i: |- ( ph -> ( S i^i W ) = { .0. } )
  assume pgpfac1.ss: |- ( ph -> ( S .(+) W ) C_ U )
  assume pgpfac1.2: |- ( ph -> A. w e. ( SubGrp ` G ) ( ( w C. U /\ A e. w ) -> -. ( S .(+) W ) C. w ) )

  disjoint A w
  disjoint .(+) w
  disjoint P w
  disjoint G w
  disjoint U w
  disjoint C w
  disjoint S w
  disjoint W w
  disjoint ph w
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
  disjoint .0. t
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
  disjoint A t
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
  disjoint .(+) t
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
  disjoint P t
  disjoint P y
  disjoint B a
  disjoint k n
  disjoint B k
  disjoint n s
  disjoint n v
  disjoint B n
  disjoint B s
  disjoint B t
  disjoint B v
  disjoint G a
  disjoint G b
  disjoint G k
  disjoint n u
  disjoint G n
  disjoint G s
  disjoint G t
  disjoint G u
  disjoint G v
  disjoint G x
  disjoint G y
  disjoint U b
  disjoint U k
  disjoint U s
  disjoint U t
  disjoint U u
  disjoint U v
  disjoint U y
  disjoint C a
  disjoint C k
  disjoint C s
  disjoint C t
  disjoint S a
  disjoint S b
  disjoint S k
  disjoint S n
  disjoint S s
  disjoint S t
  disjoint S u
  disjoint S v
  disjoint S x
  disjoint S y
  disjoint W a
  disjoint W b
  disjoint W k
  disjoint W n
  disjoint W s
  disjoint W t
  disjoint W x
  disjoint W y
  disjoint a ph
  disjoint b ph
  disjoint k ph
  disjoint n ph
  disjoint ph s
  disjoint ph t
  disjoint ph u
  disjoint ph v
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
  disjoint K t
  disjoint K x
  disjoint K y
  assert |- ( ( ph /\ C e. ( U \ ( S .(+) W ) ) ) -> ( ( S .(+) W ) .(+) ( K ` { C } ) ) = U )

  proof
    wph
    cC
    cU
    cS
    cW
    c.po
    co
    #
    cdif
    wcel
    #
    wa
    #
    @0
    cC
    csn
    #
    cK
    cfv
    #
    c.po
    co
    #
    cU
    wss
    #
    @5
    cU
    wceq
    #
    @2
    @0
    cU
    wss
    #
    @4
    cU
    wss
    #
    @6
    wph
    @8
    @1
    pgpfac1.ss
    adantr
    @2
    cG
    csubg
    cfv
    #
    cB
    cmre
    cfv
    wcel
    #
    @3
    cU
    wss
    cU
    @10
    wcel
    #
    @9
    wph
    @11
    @1
    wph
    cG
    cabl
    wcel
    #
    cG
    cgrp
    wcel
    @10
    cB
    cacs
    cfv
    wcel
    @11
    pgpfac1.g
    cG
    ablgrp
    cB
    cG
    pgpfac1.b
    subgacs
    @10
    cB
    acsmre
    4syl
    #
    adantr
    #
    @2
    cC
    cU
    @1
    cC
    cU
    wcel
    #
    wph
    cC
    cU
    @0
    eldifi
    #
    adantl
    snssd
    wph
    @12
    @1
    pgpfac1.u
    adantr
    #
    @10
    @3
    cK
    cU
    cB
    pgpfac1.k
    mrcsscl
    syl3anc
    @2
    @0
    @10
    wcel
    #
    @4
    @10
    wcel
    #
    @12
    @8
    @9
    wa
    @6
    wb
    wph
    @19
    @1
    wph
    @13
    cS
    @10
    wcel
    #
    cW
    @10
    wcel
    #
    @19
    pgpfac1.g
    wph
    cS
    cA
    csn
    #
    cK
    cfv
    #
    @10
    pgpfac1.s
    wph
    @11
    cA
    cB
    wcel
    @24
    @10
    wcel
    @14
    wph
    cU
    cB
    cA
    wph
    @12
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
    @10
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
    lsmsubg2
    syl3anc
    adantr
    #
    @2
    @11
    cC
    cB
    wcel
    #
    @20
    @15
    @1
    wph
    @16
    @29
    @17
    wph
    cU
    cB
    cC
    @25
    sselda
    sylan2
    #
    @10
    cC
    cK
    cB
    pgpfac1.k
    mrcsncl
    syl2anc
    #
    @18
    c.po
    @0
    @4
    cU
    cG
    pgpfac1.l
    lsmlub
    syl3anc
    mpbi2and
    @2
    @5
    cU
    wpss
    #
    wn
    @6
    @7
    wi
    @2
    @32
    @0
    @5
    wpss
    #
    @2
    @0
    @5
    cC
    @2
    @19
    @20
    @0
    @5
    wss
    @28
    @31
    c.po
    @0
    @4
    cG
    pgpfac1.l
    lsmub1
    syl2anc
    #
    @2
    @4
    @5
    cC
    @2
    @19
    @20
    @4
    @5
    wss
    @28
    @31
    c.po
    @0
    @4
    cG
    pgpfac1.l
    lsmub2
    syl2anc
    @2
    cC
    @4
    wcel
    #
    @3
    @4
    wss
    #
    @2
    @10
    @3
    cK
    cB
    @15
    pgpfac1.k
    @2
    cC
    cB
    @30
    snssd
    mrcssidd
    @2
    @29
    @35
    @36
    wb
    @30
    cC
    @4
    cB
    snssg
    syl
    mpbird
    sseldd
    @1
    cC
    @0
    wcel
    wn
    wph
    cC
    cU
    @0
    eldifn
    adantl
    ssnelpssd
    @2
    @32
    cA
    @5
    wcel
    #
    @33
    wn
    #
    @2
    @0
    @5
    cA
    @34
    wph
    cA
    @0
    wcel
    @1
    wph
    cS
    @0
    cA
    wph
    @21
    @22
    cS
    @0
    wss
    @27
    pgpfac1.w
    c.po
    cS
    cW
    cG
    pgpfac1.l
    lsmub1
    syl2anc
    wph
    cA
    cS
    wcel
    #
    @23
    cS
    wss
    #
    wph
    @23
    @24
    cS
    wph
    @10
    @23
    cK
    cB
    @14
    pgpfac1.k
    wph
    cA
    cB
    @26
    snssd
    mrcssidd
    pgpfac1.s
    syl6sseqr
    wph
    cA
    cU
    wcel
    @39
    @40
    wb
    pgpfac1.au
    cA
    cS
    cU
    snssg
    syl
    mpbird
    sseldd
    adantr
    sseldd
    @2
    @5
    @10
    wcel
    #
    vw
    cv
    #
    cU
    wpss
    #
    cA
    @42
    wcel
    #
    wa
    #
    @0
    @42
    wpss
    #
    wn
    #
    wi
    #
    vw
    @10
    wral
    #
    @32
    @37
    wa
    #
    @38
    wi
    #
    @2
    @13
    @19
    @20
    @41
    wph
    @13
    @1
    pgpfac1.g
    adantr
    @28
    @31
    c.po
    @0
    @4
    cG
    pgpfac1.l
    lsmsubg2
    syl3anc
    wph
    @49
    @1
    pgpfac1.2
    adantr
    @48
    @51
    vw
    @5
    @10
    @42
    @5
    wceq
    #
    @45
    @50
    @47
    @38
    @52
    @43
    @32
    @44
    @37
    @42
    @5
    cU
    psseq1
    @42
    @5
    cA
    eleq2
    anbi12d
    @52
    @46
    @33
    @42
    @5
    @0
    psseq2
    notbid
    imbi12d
    rspcv
    sylc
    mpan2d
    mt2d
    @5
    cU
    npss
    sylib
    mpd
end
