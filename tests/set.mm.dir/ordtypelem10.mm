include "cdm.mm"
include "crn.mm"
include "cep.mm"
include "wiso.mm"
include "ordtypelem8.mm"
include "wceq.mm"
include "wb.mm"
include "cin.mm"
include "wf.mm"
include "wss.mm"
include "ordtypelem4.mm"
include "frn.mm"
include "syl.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wn.mm"
include "simprl.mm"
include "wf1o.mm"
include "wfo.mm"
include "wwe.mm"
include "adantr.mm"
include "wse.mm"
include "cvv.mm"
include "isof1o.mm"
include "f1of.mm"
include "3syl.mm"
include "wf1.mm"
include "f1of1.mm"
include "wbr.mm"
include "crab.mm"
include "simpl.mm"
include "seex.mm"
include "syl2an.mm"
include "wral.mm"
include "cfv.mm"
include "wrex.mm"
include "rexnal.mm"
include "ordtypelem7.mm"
include "ord.mm"
include "rexlimdva.mm"
include "syl5bir.mm"
include "con1d.mm"
include "impr.mm"
include "wfn.mm"
include "wfun.mm"
include "ffun.mm"
include "funfn.mm"
include "sylib.mm"
include "breq1.mm"
include "ralrn.mm"
include "mpbird.mm"
include "ssrab.mm"
include "sylanbrc.mm"
include "ssexd.mm"
include "f1dmex.mm"
include "syl2anc.mm"
include "fex.mm"
include "ordtypelem9.mm"
include "f1ofo.mm"
include "forn.mm"
include "4syl.mm"
include "eleqtrrd.mm"
include "expr.mm"
include "pm2.18d.mm"
include "ex.mm"
include "ssrdv.mm"
include "eqssd.mm"
include "isoeq5.mm"
include "mpbid.mm"

theorem ordtypelem10
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let vt: setvar t
  let cA: class A
  let cC: class C
  let cR: class R
  let cT: class T
  let vh: setvar h
  let vj: setvar j
  let cF: class F
  let cG: class G
  let cO: class O
  let vf: setvar f
  let vr: setvar r
  let vs: setvar s
  let va: setvar a
  let cM: class M
  let vb: setvar b
  let cN: class N
  let vc: setvar c
  let vi: setvar i
  let vm: setvar m
  let vy: setvar y
  assume ordtypelem.1: |- F = recs ( G )
  assume ordtypelem.2: |- C = { w e. A | A. j e. ran h j R w }
  assume ordtypelem.3: |- G = ( h e. _V |-> ( iota_ v e. C A. u e. C -. u R v ) )
  assume ordtypelem.5: |- T = { x e. On | E. t e. A A. z e. ( F " x ) z R t }
  assume ordtypelem.6: |- O = OrdIso ( R , A )
  assume ordtypelem.7: |- ( ph -> R We A )
  assume ordtypelem.8: |- ( ph -> R Se A )

  disjoint u v
  disjoint C u
  disjoint C v
  disjoint h j
  disjoint h t
  disjoint h u
  disjoint h v
  disjoint h w
  disjoint h x
  disjoint h z
  disjoint j t
  disjoint j u
  disjoint j v
  disjoint j w
  disjoint j x
  disjoint j z
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t z
  disjoint u w
  disjoint u x
  disjoint u z
  disjoint v w
  disjoint v x
  disjoint v z
  disjoint w x
  disjoint w z
  disjoint x z
  disjoint R h
  disjoint R j
  disjoint R t
  disjoint R u
  disjoint R v
  disjoint R w
  disjoint R x
  disjoint R z
  disjoint A h
  disjoint A j
  disjoint A t
  disjoint A u
  disjoint A v
  disjoint A w
  disjoint A x
  disjoint A z
  disjoint O t
  disjoint O u
  disjoint O v
  disjoint O x
  disjoint ph t
  disjoint ph x
  disjoint F h
  disjoint F j
  disjoint F t
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint F x
  disjoint F z
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
  disjoint a h
  disjoint a j
  disjoint a t
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a z
  disjoint M a
  disjoint M h
  disjoint M j
  disjoint M t
  disjoint M u
  disjoint M v
  disjoint M w
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
  disjoint f h
  disjoint f i
  disjoint f j
  disjoint f m
  disjoint f t
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint R f
  disjoint h i
  disjoint h m
  disjoint h r
  disjoint h s
  disjoint h y
  disjoint i j
  disjoint i m
  disjoint i r
  disjoint i s
  disjoint i t
  disjoint i u
  disjoint i v
  disjoint i w
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint R i
  disjoint j m
  disjoint j r
  disjoint j s
  disjoint j y
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
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint R r
  disjoint s t
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint R s
  disjoint t y
  disjoint u y
  disjoint v y
  disjoint w y
  disjoint x y
  disjoint y z
  disjoint R y
  disjoint T a
  disjoint T b
  disjoint T c
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint A m
  disjoint A r
  disjoint A s
  disjoint A y
  disjoint O a
  disjoint O b
  disjoint O c
  disjoint O m
  disjoint a ph
  disjoint b ph
  disjoint m ph
  disjoint F a
  disjoint F b
  disjoint F c
  assert |- ( ph -> O Isom _E , R ( dom O , A ) )

  proof
    wph
    cO
    cdm
    #
    cO
    crn
    #
    cep
    cR
    cO
    wiso
    #
    @0
    cA
    cep
    cR
    cO
    wiso
    #
    wph
    vx
    vz
    vw
    vv
    vu
    vt
    cA
    cC
    cR
    cT
    vh
    vj
    cF
    cG
    cO
    ordtypelem.1
    ordtypelem.2
    ordtypelem.3
    ordtypelem.5
    ordtypelem.6
    ordtypelem.7
    ordtypelem.8
    ordtypelem8
    wph
    @1
    cA
    wceq
    #
    @2
    @3
    wb
    wph
    @1
    cA
    wph
    cT
    cF
    cdm
    cin
    #
    cA
    cO
    wf
    #
    @1
    cA
    wss
    #
    wph
    vx
    vz
    vw
    vv
    vu
    vt
    cA
    cC
    cR
    cT
    vh
    vj
    cF
    cG
    cO
    ordtypelem.1
    ordtypelem.2
    ordtypelem.3
    ordtypelem.5
    ordtypelem.6
    ordtypelem.7
    ordtypelem.8
    ordtypelem4
    #
    @5
    cA
    cO
    frn
    syl
    #
    wph
    vb
    cA
    @1
    wph
    vb
    cv
    #
    cA
    wcel
    #
    @10
    @1
    wcel
    #
    wph
    @11
    wa
    #
    @12
    wph
    @11
    @12
    wn
    #
    @12
    wph
    @11
    @14
    wa
    #
    wa
    #
    @10
    cA
    @1
    wph
    @11
    @14
    simprl
    @16
    @3
    @0
    cA
    cO
    wf1o
    @0
    cA
    cO
    wfo
    @4
    @16
    vx
    vz
    vw
    vv
    vu
    vt
    cA
    cC
    cR
    cT
    vh
    vj
    cF
    cG
    cO
    ordtypelem.1
    ordtypelem.2
    ordtypelem.3
    ordtypelem.5
    ordtypelem.6
    wph
    cA
    cR
    wwe
    @15
    ordtypelem.7
    adantr
    #
    wph
    cA
    cR
    wse
    #
    @15
    ordtypelem.8
    adantr
    #
    @16
    @0
    @1
    cO
    wf
    #
    @0
    cvv
    wcel
    #
    cO
    cvv
    wcel
    @16
    @2
    @0
    @1
    cO
    wf1o
    #
    @20
    @16
    vx
    vz
    vw
    vv
    vu
    vt
    cA
    cC
    cR
    cT
    vh
    vj
    cF
    cG
    cO
    ordtypelem.1
    ordtypelem.2
    ordtypelem.3
    ordtypelem.5
    ordtypelem.6
    @17
    @19
    ordtypelem8
    #
    @0
    @1
    cep
    cR
    cO
    isof1o
    #
    @0
    @1
    cO
    f1of
    3syl
    @16
    @0
    @1
    cO
    wf1
    #
    @1
    cvv
    wcel
    @21
    @16
    @2
    @22
    @25
    @23
    @24
    @0
    @1
    cO
    f1of1
    3syl
    @16
    @1
    vc
    cv
    #
    @10
    cR
    wbr
    #
    vc
    cA
    crab
    #
    cvv
    wph
    @18
    @11
    @28
    cvv
    wcel
    @15
    ordtypelem.8
    @11
    @14
    simpl
    vc
    cA
    @10
    cR
    seex
    syl2an
    @16
    @7
    @27
    vc
    @1
    wral
    #
    @1
    @28
    wss
    wph
    @7
    @15
    @9
    adantr
    @16
    @29
    vm
    cv
    #
    cO
    cfv
    #
    @10
    cR
    wbr
    #
    vm
    @0
    wral
    #
    wph
    @11
    @14
    @33
    @13
    @33
    @12
    @33
    wn
    @32
    wn
    #
    vm
    @0
    wrex
    @13
    @12
    @32
    vm
    @0
    rexnal
    @13
    @34
    @12
    vm
    @0
    @13
    @30
    @0
    wcel
    wa
    @32
    @12
    wph
    vx
    vz
    vw
    vv
    vu
    vt
    cA
    cC
    cR
    cT
    vh
    vj
    cF
    cG
    @30
    @10
    cO
    ordtypelem.1
    ordtypelem.2
    ordtypelem.3
    ordtypelem.5
    ordtypelem.6
    ordtypelem.7
    ordtypelem.8
    ordtypelem7
    ord
    rexlimdva
    syl5bir
    con1d
    impr
    @16
    cO
    @0
    wfn
    #
    @29
    @33
    wb
    wph
    @35
    @15
    wph
    cO
    wfun
    #
    @35
    wph
    @6
    @36
    @8
    @5
    cA
    cO
    ffun
    syl
    cO
    funfn
    sylib
    adantr
    @27
    @32
    vc
    vm
    @0
    cO
    @26
    @31
    @10
    cR
    breq1
    ralrn
    syl
    mpbird
    @27
    vc
    cA
    @1
    ssrab
    sylanbrc
    ssexd
    @0
    @1
    cvv
    cO
    f1dmex
    syl2anc
    @0
    @1
    cvv
    cO
    fex
    syl2anc
    ordtypelem9
    @0
    cA
    cep
    cR
    cO
    isof1o
    @0
    cA
    cO
    f1ofo
    @0
    cA
    cO
    forn
    4syl
    eleqtrrd
    expr
    pm2.18d
    ex
    ssrdv
    eqssd
    @0
    @1
    cA
    cep
    cR
    cO
    isoeq5
    syl
    mpbid
end
