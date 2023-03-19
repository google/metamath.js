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
include "wne.mm"
include "wrex.mm"
include "csubg.mm"
include "cfv.mm"
include "cmpt.mm"
include "cabl.mm"
include "wcel.mm"
include "cgrp.mm"
include "ablgrp.mm"
include "subgid.mm"
include "chash.mm"
include "cdvds.mm"
include "cprime.mm"
include "cod.mm"
include "cpc.mm"
include "cexp.mm"
include "eqid.mm"
include "ablfaclem1.mm"
include "4syl.mm"
include "ablfaclem3.mm"
include "eqnetrrd.mm"
include "rabn0.mm"
include "sylib.mm"

theorem ablfac
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cG: class G
  let vs: setvar s
  let vr: setvar r
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vf: setvar f
  let vh: setvar h
  let vp: setvar p
  let vq: setvar q
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cF: class F
  let vg: setvar g
  let cS: class S
  let vj: setvar j
  let vk: setvar k
  let vn: setvar n
  let vw: setvar w
  let cO: class O
  let c.x: class .x.
  let cW: class W
  let cH: class H
  let cU: class U
  assume ablfac.b: |- B = ( Base ` G )
  assume ablfac.c: |- C = { r e. ( SubGrp ` G ) | ( G |`s r ) e. ( CycGrp i^i ran pGrp ) }
  assume ablfac.1: |- ( ph -> G e. Abel )
  assume ablfac.2: |- ( ph -> B e. Fin )

  disjoint r s
  disjoint B r
  disjoint B s
  disjoint C s
  disjoint ph s
  disjoint G r
  disjoint G s
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
  disjoint p s
  disjoint p t
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint A p
  disjoint q s
  disjoint q t
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint A q
  disjoint s t
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint A t
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint F s
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
  disjoint g r
  disjoint g s
  disjoint g t
  disjoint g y
  disjoint S g
  disjoint h r
  disjoint S h
  disjoint q r
  disjoint S q
  disjoint r t
  disjoint r y
  disjoint S r
  disjoint S s
  disjoint S t
  disjoint S y
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
  disjoint g p
  disjoint g w
  disjoint g x
  disjoint B g
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
  disjoint p r
  disjoint p w
  disjoint B p
  disjoint r w
  disjoint r x
  disjoint s w
  disjoint t w
  disjoint B t
  disjoint w x
  disjoint B w
  disjoint B x
  disjoint O b
  disjoint O c
  disjoint O p
  disjoint O x
  disjoint .x. j
  disjoint .x. k
  disjoint .x. w
  disjoint .x. x
  disjoint C a
  disjoint C b
  disjoint C c
  disjoint C f
  disjoint g z
  disjoint C g
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
  disjoint C p
  disjoint q w
  disjoint C q
  disjoint C t
  disjoint w y
  disjoint w z
  disjoint C w
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint W a
  disjoint W b
  disjoint W c
  disjoint W f
  disjoint W h
  disjoint W p
  disjoint W q
  disjoint W t
  disjoint W w
  disjoint W x
  disjoint W y
  disjoint H s
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint f ph
  disjoint h ph
  disjoint j ph
  disjoint k ph
  disjoint n ph
  disjoint p ph
  disjoint ph q
  disjoint ph t
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint U g
  disjoint U s
  disjoint G a
  disjoint G b
  disjoint G c
  disjoint G g
  disjoint G j
  disjoint G k
  disjoint G n
  disjoint G p
  disjoint r z
  disjoint G t
  disjoint G w
  disjoint G x
  disjoint G y
  disjoint G z
  assert |- ( ph -> E. s e. Word C ( G dom DProd s /\ ( G DProd s ) = B ) )

  proof
    wph
    cG
    vs
    cv
    #
    cdprd
    cdm
    wbr
    #
    cG
    @0
    cdprd
    co
    #
    cB
    wceq
    wa
    #
    vs
    cC
    cword
    #
    crab
    #
    c0
    wne
    @3
    vs
    @4
    wrex
    wph
    cB
    vg
    cG
    csubg
    cfv
    #
    @1
    @2
    vg
    cv
    wceq
    wa
    vs
    @4
    crab
    cmpt
    #
    cfv
    #
    @5
    c0
    wph
    cG
    cabl
    wcel
    cG
    cgrp
    wcel
    cB
    @6
    wcel
    @8
    @5
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
    vw
    cv
    cB
    chash
    cfv
    #
    cdvds
    wbr
    vw
    cprime
    crab
    #
    cB
    cC
    vp
    @10
    vx
    cv
    cG
    cod
    cfv
    #
    cfv
    vp
    cv
    #
    @12
    @9
    cpc
    co
    cexp
    co
    cdvds
    wbr
    vx
    cB
    crab
    cmpt
    #
    cB
    vg
    cG
    @11
    @7
    vs
    vr
    vp
    ablfac.b
    ablfac.c
    ablfac.1
    ablfac.2
    @11
    eqid
    #
    @10
    eqid
    #
    @13
    eqid
    #
    @7
    eqid
    #
    ablfaclem1
    4syl
    wph
    vx
    vw
    @10
    cB
    cC
    @13
    vg
    cG
    @11
    @7
    vs
    vr
    vp
    ablfac.b
    ablfac.c
    ablfac.1
    ablfac.2
    @14
    @15
    @16
    @17
    ablfaclem3
    eqnetrrd
    @3
    vs
    @4
    rabn0
    sylib
end
