include "crecs.mm"
include "cvv.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "crn.mm"
include "wral.mm"
include "crab.mm"
include "crio.mm"
include "cmpt.mm"
include "wceq.mm"
include "weq.mm"
include "breq1.mm"
include "notbid.mm"
include "cbvralv.mm"
include "breq2.mm"
include "ralbidv.mm"
include "syl5bb.mm"
include "cbvriotav.mm"
include "cbvrabv.mm"
include "eqtri.mm"
include "rneq.mm"
include "raleqdv.mm"
include "rabbidv.mm"
include "syl5eq.mm"
include "riotaeqbidv.mm"
include "cbvmptv.mm"
include "recseq.mm"
include "ax-mp.mm"
include "eqtr2i.mm"

theorem ordtypecbv
  let vy: setvar y
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cC: class C
  let cR: class R
  let vf: setvar f
  let vh: setvar h
  let vi: setvar i
  let vj: setvar j
  let cF: class F
  let cG: class G
  let vs: setvar s
  let vr: setvar r
  let va: setvar a
  let vt: setvar t
  let vx: setvar x
  let vz: setvar z
  let cM: class M
  let vb: setvar b
  let cN: class N
  let vc: setvar c
  let vm: setvar m
  let cT: class T
  let cO: class O
  let wph: wff ph
  assume ordtypelem.1: |- F = recs ( G )
  assume ordtypelem.2: |- C = { w e. A | A. j e. ran h j R w }
  assume ordtypelem.3: |- G = ( h e. _V |-> ( iota_ v e. C A. u e. C -. u R v ) )

  disjoint f r
  disjoint f s
  disjoint f u
  disjoint f v
  disjoint C f
  disjoint r s
  disjoint r u
  disjoint r v
  disjoint C r
  disjoint s u
  disjoint s v
  disjoint C s
  disjoint u v
  disjoint C u
  disjoint C v
  disjoint h j
  disjoint h u
  disjoint h v
  disjoint h w
  disjoint j u
  disjoint j v
  disjoint j w
  disjoint u w
  disjoint v w
  disjoint f h
  disjoint f i
  disjoint f j
  disjoint f w
  disjoint f y
  disjoint R f
  disjoint h i
  disjoint h r
  disjoint h s
  disjoint h y
  disjoint R h
  disjoint i j
  disjoint i r
  disjoint i s
  disjoint i u
  disjoint i v
  disjoint i w
  disjoint i y
  disjoint R i
  disjoint j r
  disjoint j s
  disjoint j y
  disjoint R j
  disjoint r w
  disjoint r y
  disjoint R r
  disjoint s w
  disjoint s y
  disjoint R s
  disjoint u y
  disjoint R u
  disjoint v y
  disjoint R v
  disjoint w y
  disjoint R w
  disjoint R y
  disjoint A h
  disjoint A j
  disjoint A r
  disjoint A s
  disjoint A u
  disjoint A v
  disjoint A w
  disjoint A y
  disjoint a h
  disjoint a j
  disjoint a t
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a z
  disjoint M a
  disjoint h t
  disjoint h x
  disjoint h z
  disjoint M h
  disjoint j t
  disjoint j x
  disjoint j z
  disjoint M j
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t z
  disjoint M t
  disjoint u x
  disjoint u z
  disjoint M u
  disjoint v x
  disjoint v z
  disjoint M v
  disjoint w x
  disjoint w z
  disjoint M w
  disjoint x z
  disjoint M x
  disjoint M z
  disjoint a b
  disjoint N a
  disjoint b j
  disjoint b u
  disjoint b w
  disjoint N b
  disjoint N j
  disjoint N u
  disjoint N w
  disjoint a c
  disjoint a f
  disjoint a i
  disjoint a m
  disjoint a r
  disjoint a s
  disjoint a y
  disjoint R a
  disjoint b c
  disjoint b f
  disjoint b h
  disjoint b i
  disjoint b m
  disjoint b r
  disjoint b s
  disjoint b t
  disjoint b v
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint R b
  disjoint c f
  disjoint c h
  disjoint c i
  disjoint c j
  disjoint c m
  disjoint c r
  disjoint c s
  disjoint c t
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint R c
  disjoint f m
  disjoint f t
  disjoint f x
  disjoint f z
  disjoint h m
  disjoint i m
  disjoint i t
  disjoint i x
  disjoint i z
  disjoint j m
  disjoint m r
  disjoint m s
  disjoint m t
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint R m
  disjoint r t
  disjoint r x
  disjoint r z
  disjoint s t
  disjoint s x
  disjoint s z
  disjoint t y
  disjoint R t
  disjoint x y
  disjoint R x
  disjoint y z
  disjoint R z
  disjoint T a
  disjoint T b
  disjoint T c
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint A m
  disjoint A t
  disjoint A x
  disjoint A z
  disjoint O a
  disjoint O b
  disjoint O c
  disjoint O m
  disjoint O t
  disjoint O u
  disjoint O v
  disjoint O x
  disjoint a ph
  disjoint b ph
  disjoint m ph
  disjoint ph t
  disjoint ph x
  assert |- recs ( ( f e. _V |-> ( iota_ s e. { y e. A | A. i e. ran f i R y } A. r e. { y e. A | A. i e. ran f i R y } -. r R s ) ) ) = F

  proof
    cF
    cG
    crecs
    #
    vf
    cvv
    vr
    cv
    #
    vs
    cv
    #
    cR
    wbr
    #
    wn
    #
    vr
    vi
    cv
    #
    vy
    cv
    #
    cR
    wbr
    #
    vi
    vf
    cv
    #
    crn
    #
    wral
    #
    vy
    cA
    crab
    #
    wral
    #
    vs
    @11
    crio
    #
    cmpt
    #
    crecs
    #
    ordtypelem.1
    cG
    @14
    wceq
    @0
    @15
    wceq
    cG
    vh
    cvv
    vu
    cv
    #
    vv
    cv
    #
    cR
    wbr
    #
    wn
    #
    vu
    cC
    wral
    #
    vv
    cC
    crio
    #
    cmpt
    @14
    ordtypelem.3
    vh
    vf
    cvv
    @21
    @13
    vh
    vf
    weq
    #
    @21
    @4
    vr
    cC
    wral
    #
    vs
    cC
    crio
    @13
    @20
    @23
    vv
    vs
    cC
    @20
    @1
    @17
    cR
    wbr
    #
    wn
    #
    vr
    cC
    wral
    vv
    vs
    weq
    #
    @23
    @19
    @25
    vu
    vr
    cC
    vu
    vr
    weq
    @18
    @24
    @16
    @1
    @17
    cR
    breq1
    notbid
    cbvralv
    @26
    @25
    @4
    vr
    cC
    @26
    @24
    @3
    @17
    @2
    @1
    cR
    breq2
    notbid
    ralbidv
    syl5bb
    cbvriotav
    @22
    @23
    @12
    vs
    cC
    @11
    @22
    cC
    @7
    vi
    vh
    cv
    #
    crn
    #
    wral
    #
    vy
    cA
    crab
    #
    @11
    cC
    vj
    cv
    #
    vw
    cv
    #
    cR
    wbr
    #
    vj
    @28
    wral
    #
    vw
    cA
    crab
    @30
    ordtypelem.2
    @34
    @29
    vw
    vy
    cA
    @34
    @5
    @32
    cR
    wbr
    #
    vi
    @28
    wral
    vw
    vy
    weq
    #
    @29
    @33
    @35
    vj
    vi
    @28
    @31
    @5
    @32
    cR
    breq1
    cbvralv
    @36
    @35
    @7
    vi
    @28
    @32
    @6
    @5
    cR
    breq2
    ralbidv
    syl5bb
    cbvrabv
    eqtri
    @22
    @29
    @10
    vy
    cA
    @22
    @7
    vi
    @28
    @9
    @27
    @8
    rneq
    raleqdv
    rabbidv
    syl5eq
    #
    @22
    @4
    vr
    cC
    @11
    @37
    raleqdv
    riotaeqbidv
    syl5eq
    cbvmptv
    eqtri
    cG
    @14
    recseq
    ax-mp
    eqtr2i
end
