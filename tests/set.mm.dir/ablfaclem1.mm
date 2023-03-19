include "cv.mm"
include "cdprd.mm"
include "cdm.mm"
include "wbr.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "cword.mm"
include "crab.mm"
include "csubg.mm"
include "cfv.mm"
include "eqeq2.mm"
include "anbi2d.mm"
include "rabbidv.mm"
include "cvv.mm"
include "wcel.mm"
include "cress.mm"
include "ccyg.mm"
include "cpgp.mm"
include "crn.mm"
include "cin.mm"
include "fvex.mm"
include "rabex2.mm"
include "wrdexg.mm"
include "ax-mp.mm"
include "rabex.mm"
include "fvmpt.mm"

theorem ablfaclem1
  let wph: wff ph
  let vx: setvar x
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let cU: class U
  let vg: setvar g
  let cG: class G
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
  let vy: setvar y
  let vz: setvar z
  let cF: class F
  let vj: setvar j
  let vk: setvar k
  let vn: setvar n
  let c.x: class .x.
  let cH: class H
  assume ablfac.b: |- B = ( Base ` G )
  assume ablfac.c: |- C = { r e. ( SubGrp ` G ) | ( G |`s r ) e. ( CycGrp i^i ran pGrp ) }
  assume ablfac.1: |- ( ph -> G e. Abel )
  assume ablfac.2: |- ( ph -> B e. Fin )
  assume ablfac.o: |- O = ( od ` G )
  assume ablfac.a: |- A = { w e. Prime | w || ( # ` B ) }
  assume ablfac.s: |- S = ( p e. A |-> { x e. B | ( O ` x ) || ( p ^ ( p pCnt ( # ` B ) ) ) } )
  assume ablfac.w: |- W = ( g e. ( SubGrp ` G ) |-> { s e. Word C | ( G dom DProd s /\ ( G DProd s ) = g ) } )

  disjoint p s
  disjoint p x
  disjoint A p
  disjoint s x
  disjoint A s
  disjoint A x
  disjoint g r
  disjoint g s
  disjoint S g
  disjoint r s
  disjoint S r
  disjoint S s
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
  disjoint C w
  disjoint C x
  disjoint W p
  disjoint W w
  disjoint W x
  disjoint p ph
  disjoint ph s
  disjoint ph w
  disjoint ph x
  disjoint U g
  disjoint U s
  disjoint G g
  disjoint G p
  disjoint G r
  disjoint G s
  disjoint G w
  disjoint G x
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
  disjoint p y
  disjoint p z
  disjoint q s
  disjoint q t
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint A q
  disjoint s t
  disjoint s y
  disjoint s z
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint A t
  disjoint x y
  disjoint x z
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
  disjoint g t
  disjoint g y
  disjoint h r
  disjoint S h
  disjoint q r
  disjoint S q
  disjoint r t
  disjoint r y
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
  disjoint w y
  disjoint w z
  disjoint C y
  disjoint C z
  disjoint W a
  disjoint W b
  disjoint W c
  disjoint W f
  disjoint W h
  disjoint W q
  disjoint W t
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
  disjoint ph q
  disjoint ph t
  disjoint ph y
  disjoint ph z
  disjoint G a
  disjoint G b
  disjoint G c
  disjoint G j
  disjoint G k
  disjoint G n
  disjoint r z
  disjoint G t
  disjoint G y
  disjoint G z
  assert |- ( U e. ( SubGrp ` G ) -> ( W ` U ) = { s e. Word C | ( G dom DProd s /\ ( G DProd s ) = U ) } )

  proof
    vg
    cU
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
    vg
    cv
    #
    wceq
    #
    wa
    #
    vs
    cC
    cword
    #
    crab
    @1
    @2
    cU
    wceq
    #
    wa
    #
    vs
    @6
    crab
    cG
    csubg
    cfv
    #
    cW
    @3
    cU
    wceq
    #
    @5
    @8
    vs
    @6
    @10
    @4
    @7
    @1
    @3
    cU
    @2
    eqeq2
    anbi2d
    rabbidv
    ablfac.w
    @8
    vs
    @6
    cC
    cvv
    wcel
    @6
    cvv
    wcel
    cG
    vr
    cv
    cress
    co
    ccyg
    cpgp
    crn
    cin
    wcel
    vr
    @9
    cC
    ablfac.c
    cG
    csubg
    fvex
    rabex2
    cC
    cvv
    wrdexg
    ax-mp
    rabex
    fvmpt
end
