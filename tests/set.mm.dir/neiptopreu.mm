include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "csn.mm"
include "cnei.mm"
include "cmpt.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wreu.mm"
include "cuni.mm"
include "ctop.mm"
include "neiptoptop.mm"
include "eqid.mm"
include "toptopon.mm"
include "sylib.mm"
include "neiptopuni.mm"
include "fveq2d.mm"
include "eleqtrrd.mm"
include "neiptopnei.mm"
include "wa.mm"
include "wss.mm"
include "nfv.mm"
include "nfmpt1.mm"
include "nfeq2.mm"
include "nfan.mm"
include "simpllr.mm"
include "simpr.mm"
include "sselda.mm"
include "cvv.mm"
include "id.mm"
include "fvexd.mm"
include "fvmpt2d.mm"
include "syl2anc.mm"
include "eqcomd.mm"
include "eleq2d.mm"
include "ralbida.mm"
include "pm5.32da.mm"
include "toponss.mm"
include "wb.mm"
include "topontop.mm"
include "ad2antlr.mm"
include "opnnei.mm"
include "syl.mm"
include "biimpa.mm"
include "jca.mm"
include "biimpar.mm"
include "adantrl.mm"
include "impbida.mm"
include "neipeltop.mm"
include "a1i.mm"
include "3bitr4d.mm"
include "eqrdv.mm"
include "ex.mm"
include "ralrimiva.mm"
include "simpl.mm"
include "fveq1d.mm"
include "mpteq2dva.mm"
include "eqeq2d.mm"
include "eqreu.mm"
include "syl3anc.mm"

theorem neiptopreu
  let wph: wff ph
  let vj: setvar j
  let cJ: class J
  let cN: class N
  let cX: class X
  let vq: setvar q
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let cC: class C
  let vc: setvar c
  let ve: setvar e
  let vf: setvar f
  let vd: setvar d
  let vr: setvar r
  let vs: setvar s
  assume neiptop.o: |- J = { a e. ~P X | A. p e. a a e. ( N ` p ) }
  assume neiptop.0: |- ( ph -> N : X --> ~P ~P X )
  assume neiptop.1: |- ( ( ( ( ph /\ p e. X ) /\ a C_ b /\ b C_ X ) /\ a e. ( N ` p ) ) -> b e. ( N ` p ) )
  assume neiptop.2: |- ( ( ph /\ p e. X ) -> ( fi ` ( N ` p ) ) C_ ( N ` p ) )
  assume neiptop.3: |- ( ( ( ph /\ p e. X ) /\ a e. ( N ` p ) ) -> p e. a )
  assume neiptop.4: |- ( ( ( ph /\ p e. X ) /\ a e. ( N ` p ) ) -> E. b e. ( N ` p ) A. q e. b a e. ( N ` q ) )
  assume neiptop.5: |- ( ( ph /\ p e. X ) -> X e. ( N ` p ) )

  disjoint a p
  disjoint N a
  disjoint X a
  disjoint a b
  disjoint b p
  disjoint J a
  disjoint J p
  disjoint X p
  disjoint p ph
  disjoint N b
  disjoint X b
  disjoint a ph
  disjoint b ph
  disjoint a q
  disjoint b q
  disjoint p q
  disjoint N p
  disjoint N q
  disjoint X q
  disjoint ph q
  disjoint a j
  disjoint b j
  disjoint J b
  disjoint j p
  disjoint J j
  disjoint j q
  disjoint N j
  disjoint X j
  disjoint j ph
  disjoint C a
  disjoint C p
  disjoint a c
  disjoint a e
  disjoint a f
  disjoint c e
  disjoint c f
  disjoint c p
  disjoint J c
  disjoint e f
  disjoint e p
  disjoint J e
  disjoint f p
  disjoint J f
  disjoint b c
  disjoint N c
  disjoint b e
  disjoint b f
  disjoint c ph
  disjoint e ph
  disjoint f ph
  disjoint a d
  disjoint c d
  disjoint d p
  disjoint J d
  disjoint a r
  disjoint a s
  disjoint b d
  disjoint b r
  disjoint b s
  disjoint c q
  disjoint c r
  disjoint c s
  disjoint d q
  disjoint d r
  disjoint d s
  disjoint N d
  disjoint p r
  disjoint p s
  disjoint q r
  disjoint q s
  disjoint r s
  disjoint N r
  disjoint N s
  disjoint X c
  disjoint X d
  disjoint X r
  disjoint X s
  disjoint d ph
  disjoint ph r
  disjoint ph s
  assert |- ( ph -> E! j e. ( TopOn ` X ) N = ( p e. X |-> ( ( nei ` j ) ` { p } ) ) )

  proof
    wph
    cJ
    cX
    ctopon
    cfv
    #
    wcel
    cN
    vp
    cX
    vp
    cv
    #
    csn
    #
    cJ
    cnei
    cfv
    #
    cfv
    #
    cmpt
    #
    wceq
    #
    cN
    vp
    cX
    @2
    vj
    cv
    #
    cnei
    cfv
    #
    cfv
    #
    cmpt
    #
    wceq
    #
    @7
    cJ
    wceq
    #
    wi
    #
    vj
    @0
    wral
    @11
    vj
    @0
    wreu
    wph
    cJ
    cJ
    cuni
    #
    ctopon
    cfv
    #
    @0
    wph
    cJ
    ctop
    wcel
    cJ
    @15
    wcel
    wph
    cJ
    cN
    cX
    vq
    vp
    va
    vb
    neiptop.o
    neiptop.0
    neiptop.1
    neiptop.2
    neiptop.3
    neiptop.4
    neiptop.5
    neiptoptop
    cJ
    @14
    @14
    eqid
    toptopon
    sylib
    wph
    cX
    @14
    ctopon
    wph
    cJ
    cN
    cX
    vq
    vp
    va
    vb
    neiptop.o
    neiptop.0
    neiptop.1
    neiptop.2
    neiptop.3
    neiptop.4
    neiptop.5
    neiptopuni
    fveq2d
    eleqtrrd
    wph
    cJ
    cN
    cX
    vq
    vp
    va
    vb
    neiptop.o
    neiptop.0
    neiptop.1
    neiptop.2
    neiptop.3
    neiptop.4
    neiptop.5
    neiptopnei
    wph
    @13
    vj
    @0
    wph
    @7
    @0
    wcel
    #
    wa
    #
    @11
    @12
    @17
    @11
    wa
    #
    vb
    @7
    cJ
    @18
    vb
    cv
    #
    cX
    wss
    #
    @19
    @9
    wcel
    #
    vp
    @19
    wral
    #
    wa
    #
    @20
    @19
    @1
    cN
    cfv
    #
    wcel
    #
    vp
    @19
    wral
    #
    wa
    #
    @19
    @7
    wcel
    #
    @19
    cJ
    wcel
    #
    @18
    @20
    @22
    @26
    @18
    @20
    wa
    #
    @21
    @25
    vp
    @19
    @18
    @20
    vp
    @17
    @11
    vp
    @17
    vp
    nfv
    vp
    cN
    @10
    vp
    cX
    @9
    nfmpt1
    nfeq2
    nfan
    @20
    vp
    nfv
    nfan
    @30
    @1
    @19
    wcel
    #
    wa
    #
    @9
    @24
    @19
    @32
    @24
    @9
    @32
    @11
    @1
    cX
    wcel
    #
    @24
    @9
    wceq
    @17
    @11
    @20
    @31
    simpllr
    @30
    @19
    cX
    @1
    @18
    @20
    simpr
    sselda
    @11
    vp
    cX
    @9
    cN
    cvv
    @11
    id
    @11
    @33
    wa
    @2
    @8
    fvexd
    fvmpt2d
    syl2anc
    eqcomd
    eleq2d
    ralbida
    pm5.32da
    @18
    @28
    @23
    @18
    @28
    wa
    #
    @20
    @22
    @34
    @16
    @28
    @20
    wph
    @16
    @11
    @28
    simpllr
    @18
    @28
    simpr
    @19
    @7
    cX
    toponss
    syl2anc
    @18
    @28
    @22
    @18
    @7
    ctop
    wcel
    #
    @28
    @22
    wb
    @16
    @35
    wph
    @11
    cX
    @7
    topontop
    ad2antlr
    vp
    @19
    @7
    opnnei
    syl
    #
    biimpa
    jca
    @18
    @22
    @28
    @20
    @18
    @28
    @22
    @36
    biimpar
    adantrl
    impbida
    @29
    @27
    wb
    @18
    @19
    cJ
    cN
    cX
    vp
    va
    neiptop.o
    neipeltop
    a1i
    3bitr4d
    eqrdv
    ex
    ralrimiva
    @11
    @6
    vj
    @0
    cJ
    @12
    @10
    @5
    cN
    @12
    vp
    cX
    @9
    @4
    @12
    @33
    wa
    #
    @2
    @8
    @3
    @37
    @7
    cJ
    cnei
    @12
    @33
    simpl
    fveq2d
    fveq1d
    mpteq2dva
    eqeq2d
    eqreu
    syl3anc
end
