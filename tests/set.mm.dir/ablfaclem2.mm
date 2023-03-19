include "cfv.mm"
include "cv.mm"
include "cdprd.mm"
include "cdm.mm"
include "wbr.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "cword.mm"
include "crab.mm"
include "c0.mm"
include "cabl.mm"
include "wcel.mm"
include "cgrp.mm"
include "csubg.mm"
include "ablgrp.mm"
include "subgid.mm"
include "ablfaclem1.mm"
include "4syl.mm"
include "wrex.mm"
include "wne.mm"
include "cmpt2.mm"
include "ccom.mm"
include "cc0.mm"
include "chash.mm"
include "cfzo.mm"
include "wf.mm"
include "csn.mm"
include "cxp.mm"
include "ciun.mm"
include "wral.mm"
include "ffvelrnda.mm"
include "wrdf.mm"
include "syl.mm"
include "fdm.mm"
include "feq2d.mm"
include "mpbird.mm"
include "anasss.mm"
include "ralrimivva.mm"
include "eqid.mm"
include "fmpt2x.mm"
include "sylib.mm"
include "feq2i.mm"
include "sylibr.mm"
include "wf1o.mm"
include "f1of.mm"
include "fco.mm"
include "syl2anc.mm"
include "iswrdi.mm"
include "cmpt.mm"
include "r19.21bi.mm"
include "cprime.mm"
include "wss.mm"
include "cdvds.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "a1i.mm"
include "ablfac1b.mm"
include "cpc.mm"
include "cexp.mm"
include "cbs.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "rabex.mm"
include "dmmpti.mm"
include "dprdf2.mm"
include "eleqtrd.mm"
include "breq2.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "elrab.mm"
include "simprbi.mm"
include "simpld.mm"
include "dprdf.mm"
include "feqmptd.mm"
include "breqtrd.mm"
include "oveq2d.mm"
include "simprd.mm"
include "eqtr3d.mm"
include "mpteq2dva.mm"
include "eqtr4d.mm"
include "dprd2d2.mm"
include "dprdf1o.mm"
include "ssid.mm"
include "ablfac1c.mm"
include "3eqtrd.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "rabn0.mm"
include "eqnetrd.mm"

theorem ablfaclem2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let vg: setvar g
  let cF: class F
  let cG: class G
  let cH: class H
  let cL: class L
  let cO: class O
  let cW: class W
  let vs: setvar s
  let vr: setvar r
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vf: setvar f
  let vh: setvar h
  let vq: setvar q
  let vt: setvar t
  let vz: setvar z
  let vj: setvar j
  let vk: setvar k
  let vn: setvar n
  let c.x: class .x.
  let cU: class U
  assume ablfac.b: |- B = ( Base ` G )
  assume ablfac.c: |- C = { r e. ( SubGrp ` G ) | ( G |`s r ) e. ( CycGrp i^i ran pGrp ) }
  assume ablfac.1: |- ( ph -> G e. Abel )
  assume ablfac.2: |- ( ph -> B e. Fin )
  assume ablfac.o: |- O = ( od ` G )
  assume ablfac.a: |- A = { w e. Prime | w || ( # ` B ) }
  assume ablfac.s: |- S = ( p e. A |-> { x e. B | ( O ` x ) || ( p ^ ( p pCnt ( # ` B ) ) ) } )
  assume ablfac.w: |- W = ( g e. ( SubGrp ` G ) |-> { s e. Word C | ( G dom DProd s /\ ( G DProd s ) = g ) } )
  assume ablfaclem2.f: |- ( ph -> F : A --> Word C )
  assume ablfaclem2.q: |- ( ph -> A. y e. A ( F ` y ) e. ( W ` ( S ` y ) ) )
  assume ablfaclem2.l: |- L = U_ y e. A ( { y } X. dom ( F ` y ) )
  assume ablfaclem2.g: |- ( ph -> H : ( 0 ..^ ( # ` L ) ) -1-1-onto-> L )

  disjoint p s
  disjoint p x
  disjoint p y
  disjoint A p
  disjoint s x
  disjoint s y
  disjoint A s
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint F s
  disjoint g r
  disjoint g s
  disjoint g y
  disjoint S g
  disjoint r s
  disjoint r y
  disjoint S r
  disjoint S s
  disjoint S y
  disjoint g p
  disjoint g w
  disjoint g x
  disjoint B g
  disjoint p r
  disjoint p w
  disjoint B p
  disjoint r w
  disjoint r x
  disjoint B r
  disjoint s w
  disjoint B s
  disjoint w x
  disjoint B w
  disjoint B x
  disjoint O p
  disjoint O x
  disjoint C g
  disjoint C p
  disjoint C s
  disjoint w y
  disjoint C w
  disjoint C x
  disjoint C y
  disjoint W p
  disjoint W w
  disjoint W x
  disjoint W y
  disjoint H s
  disjoint p ph
  disjoint ph s
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint G g
  disjoint G p
  disjoint G r
  disjoint G s
  disjoint G w
  disjoint G x
  disjoint G y
  disjoint a b
  disjoint a c
  disjoint a f
  disjoint a h
  disjoint a p
  disjoint a q
  disjoint a s
  disjoint a t
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint A a
  disjoint b c
  disjoint b f
  disjoint b h
  disjoint b p
  disjoint b q
  disjoint b s
  disjoint b t
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint A b
  disjoint c f
  disjoint c h
  disjoint c p
  disjoint c q
  disjoint c s
  disjoint c t
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint A c
  disjoint f h
  disjoint f p
  disjoint f q
  disjoint f s
  disjoint f t
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint h p
  disjoint h q
  disjoint h s
  disjoint h t
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint A h
  disjoint p q
  disjoint p t
  disjoint p z
  disjoint q s
  disjoint q t
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint A q
  disjoint s t
  disjoint s z
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint A t
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint F z
  disjoint a g
  disjoint a r
  disjoint S a
  disjoint b g
  disjoint b r
  disjoint S b
  disjoint c g
  disjoint c r
  disjoint S c
  disjoint f g
  disjoint f r
  disjoint S f
  disjoint g h
  disjoint g q
  disjoint g t
  disjoint h r
  disjoint S h
  disjoint q r
  disjoint S q
  disjoint r t
  disjoint S t
  disjoint a j
  disjoint a k
  disjoint a n
  disjoint a w
  disjoint B a
  disjoint b j
  disjoint b k
  disjoint b n
  disjoint b w
  disjoint B b
  disjoint c j
  disjoint c k
  disjoint c n
  disjoint c w
  disjoint B c
  disjoint f j
  disjoint f k
  disjoint f n
  disjoint f w
  disjoint B f
  disjoint g j
  disjoint g k
  disjoint g n
  disjoint h j
  disjoint h k
  disjoint h n
  disjoint h w
  disjoint B h
  disjoint j k
  disjoint j n
  disjoint j p
  disjoint j r
  disjoint j s
  disjoint j t
  disjoint j w
  disjoint j x
  disjoint B j
  disjoint k n
  disjoint k p
  disjoint k r
  disjoint k s
  disjoint k t
  disjoint k w
  disjoint k x
  disjoint B k
  disjoint n p
  disjoint n r
  disjoint n s
  disjoint n t
  disjoint n w
  disjoint n x
  disjoint B n
  disjoint t w
  disjoint B t
  disjoint O b
  disjoint O c
  disjoint .x. j
  disjoint .x. k
  disjoint .x. w
  disjoint .x. x
  disjoint C a
  disjoint C b
  disjoint C c
  disjoint C f
  disjoint g z
  disjoint C h
  disjoint j q
  disjoint j y
  disjoint j z
  disjoint C j
  disjoint k q
  disjoint k y
  disjoint k z
  disjoint C k
  disjoint n q
  disjoint n y
  disjoint n z
  disjoint C n
  disjoint q w
  disjoint C q
  disjoint C t
  disjoint w z
  disjoint C z
  disjoint W a
  disjoint W b
  disjoint W c
  disjoint W f
  disjoint W h
  disjoint W q
  disjoint W t
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint f ph
  disjoint h ph
  disjoint j ph
  disjoint k ph
  disjoint n ph
  disjoint ph q
  disjoint ph t
  disjoint ph z
  disjoint U g
  disjoint U s
  disjoint G a
  disjoint G b
  disjoint G c
  disjoint G j
  disjoint G k
  disjoint G n
  disjoint r z
  disjoint G t
  disjoint G z
  assert |- ( ph -> ( W ` B ) =/= (/) )

  proof
    wph
    cB
    cW
    cfv
    #
    cG
    vs
    cv
    #
    cdprd
    cdm
    #
    wbr
    #
    cG
    @1
    cdprd
    co
    #
    cB
    wceq
    #
    wa
    #
    vs
    cC
    cword
    #
    crab
    #
    c0
    wph
    cG
    cabl
    wcel
    cG
    cgrp
    wcel
    cB
    cG
    csubg
    cfv
    #
    wcel
    @0
    @8
    wceq
    ablfac.1
    cG
    ablgrp
    cB
    cG
    ablfac.b
    subgid
    wph
    vx
    vw
    cA
    cB
    cC
    cS
    cB
    vg
    cG
    cO
    cW
    vs
    vr
    vp
    ablfac.b
    ablfac.c
    ablfac.1
    ablfac.2
    ablfac.o
    ablfac.a
    ablfac.s
    ablfac.w
    ablfaclem1
    4syl
    wph
    @6
    vs
    @7
    wrex
    #
    @8
    c0
    wne
    wph
    vy
    vz
    cA
    vy
    cv
    #
    cF
    cfv
    #
    cdm
    #
    vz
    cv
    #
    @12
    cfv
    #
    cmpt2
    #
    cH
    ccom
    #
    @7
    wcel
    #
    cG
    @17
    @2
    wbr
    #
    cG
    @17
    cdprd
    co
    #
    cB
    wceq
    #
    @10
    wph
    cc0
    cL
    chash
    cfv
    #
    cfzo
    co
    #
    cC
    @17
    wf
    #
    @18
    wph
    cL
    cC
    @16
    wf
    #
    @23
    cL
    cH
    wf
    #
    @24
    wph
    vy
    cA
    @11
    csn
    @13
    cxp
    ciun
    #
    cC
    @16
    wf
    #
    @25
    wph
    @15
    cC
    wcel
    #
    vz
    @13
    wral
    vy
    cA
    wral
    @28
    wph
    @29
    vy
    vz
    cA
    @13
    wph
    @11
    cA
    wcel
    #
    @14
    @13
    wcel
    #
    @29
    wph
    @30
    wa
    #
    @13
    cC
    @14
    @12
    @32
    @13
    cC
    @12
    wf
    cc0
    @12
    chash
    cfv
    cfzo
    co
    #
    cC
    @12
    wf
    #
    @32
    @12
    @7
    wcel
    #
    @34
    wph
    cA
    @7
    @11
    cF
    ablfaclem2.f
    ffvelrnda
    cC
    @12
    wrdf
    syl
    #
    @32
    @13
    @33
    cC
    @12
    @32
    @34
    @13
    @33
    wceq
    @36
    @33
    cC
    @12
    fdm
    syl
    feq2d
    mpbird
    ffvelrnda
    anasss
    ralrimivva
    vy
    vz
    cA
    @13
    @15
    cC
    @16
    @16
    eqid
    fmpt2x
    sylib
    cL
    @27
    cC
    @16
    ablfaclem2.l
    feq2i
    sylibr
    #
    wph
    @23
    cL
    cH
    wf1o
    @26
    ablfaclem2.g
    @23
    cL
    cH
    f1of
    syl
    @23
    cL
    cC
    @16
    cH
    fco
    syl2anc
    cC
    @22
    @17
    iswrdi
    syl
    wph
    @19
    @20
    cG
    @16
    cdprd
    co
    #
    wceq
    #
    wph
    @16
    cH
    cG
    cL
    @23
    wph
    cG
    @16
    @2
    wbr
    #
    @38
    cG
    vy
    cA
    cG
    vz
    @13
    @15
    cmpt
    #
    cdprd
    co
    #
    cmpt
    #
    cdprd
    co
    #
    wceq
    #
    wph
    @15
    vy
    vz
    cG
    cA
    @13
    wph
    @30
    @31
    @15
    @9
    wcel
    @32
    @13
    @9
    @14
    @12
    @32
    cG
    @12
    @2
    wbr
    #
    @13
    @9
    @12
    wf
    @32
    @46
    cG
    @12
    cdprd
    co
    #
    @11
    cS
    cfv
    #
    wceq
    #
    @32
    @12
    @3
    @4
    @48
    wceq
    #
    wa
    #
    vs
    @7
    crab
    #
    wcel
    #
    @46
    @49
    wa
    #
    @32
    @12
    @48
    cW
    cfv
    #
    @52
    wph
    @12
    @55
    wcel
    vy
    cA
    ablfaclem2.q
    r19.21bi
    @32
    @48
    @9
    wcel
    @55
    @52
    wceq
    wph
    cA
    @9
    @11
    cS
    wph
    cS
    cG
    cA
    wph
    vx
    cA
    cB
    cS
    cG
    cO
    vp
    ablfac.b
    ablfac.o
    ablfac.s
    ablfac.1
    ablfac.2
    cA
    cprime
    wss
    wph
    cA
    vw
    cv
    cB
    chash
    cfv
    #
    cdvds
    wbr
    #
    vw
    cprime
    crab
    cprime
    ablfac.a
    @57
    vw
    cprime
    ssrab2
    eqsstri
    a1i
    #
    ablfac1b
    #
    cS
    cdm
    cA
    wceq
    wph
    vp
    cA
    vx
    cv
    cO
    cfv
    vp
    cv
    #
    @60
    @56
    cpc
    co
    cexp
    co
    cdvds
    wbr
    #
    vx
    cB
    crab
    cS
    @61
    vx
    cB
    cB
    cG
    cbs
    cfv
    cvv
    ablfac.b
    cG
    cbs
    fvex
    eqeltri
    rabex
    ablfac.s
    dmmpti
    a1i
    dprdf2
    #
    ffvelrnda
    wph
    vx
    vw
    cA
    cB
    cC
    cS
    @48
    vg
    cG
    cO
    cW
    vs
    vr
    vp
    ablfac.b
    ablfac.c
    ablfac.1
    ablfac.2
    ablfac.o
    ablfac.a
    ablfac.s
    ablfac.w
    ablfaclem1
    syl
    eleqtrd
    @53
    @35
    @54
    @51
    @54
    vs
    @12
    @7
    @1
    @12
    wceq
    #
    @3
    @46
    @50
    @49
    @1
    @12
    cG
    @2
    breq2
    @63
    @4
    @47
    @48
    @1
    @12
    cG
    cdprd
    oveq2
    eqeq1d
    anbi12d
    elrab
    simprbi
    syl
    #
    simpld
    #
    @12
    cG
    dprdf
    syl
    #
    ffvelrnda
    anasss
    @32
    cG
    @12
    @41
    @2
    @65
    @32
    vz
    @13
    @9
    @12
    @66
    feqmptd
    #
    breqtrd
    wph
    cG
    cS
    @43
    @2
    @59
    wph
    cS
    vy
    cA
    @48
    cmpt
    @43
    wph
    vy
    cA
    @9
    cS
    @62
    feqmptd
    wph
    vy
    cA
    @42
    @48
    @32
    @47
    @42
    @48
    @32
    @12
    @41
    cG
    cdprd
    @67
    oveq2d
    @32
    @46
    @49
    @64
    simprd
    eqtr3d
    mpteq2dva
    eqtr4d
    #
    breqtrd
    dprd2d2
    #
    simpld
    wph
    @25
    @16
    cdm
    cL
    wceq
    @37
    cL
    cC
    @16
    fdm
    syl
    ablfaclem2.g
    dprdf1o
    #
    simpld
    wph
    @20
    @38
    @44
    cB
    wph
    @19
    @39
    @70
    simprd
    wph
    @40
    @45
    @69
    simprd
    wph
    cG
    cS
    cdprd
    co
    @44
    cB
    wph
    cS
    @43
    cG
    cdprd
    @68
    oveq2d
    wph
    vx
    vw
    cA
    cB
    cA
    cS
    cG
    cO
    vp
    ablfac.b
    ablfac.o
    ablfac.s
    ablfac.1
    ablfac.2
    @58
    ablfac.a
    cA
    cA
    wss
    wph
    cA
    ssid
    a1i
    ablfac1c
    eqtr3d
    3eqtrd
    @6
    @19
    @21
    wa
    vs
    @17
    @7
    @1
    @17
    wceq
    #
    @3
    @19
    @5
    @21
    @1
    @17
    cG
    @2
    breq2
    @71
    @4
    @20
    cB
    @1
    @17
    cG
    cdprd
    oveq2
    eqeq1d
    anbi12d
    rspcev
    syl12anc
    @6
    vs
    @7
    rabn0
    sylibr
    eqnetrd
end
