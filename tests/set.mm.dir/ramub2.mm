include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "co.mm"
include "wf.mm"
include "wa.mm"
include "c1.mm"
include "cfz.mm"
include "cen.mm"
include "wss.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cpw.mm"
include "wrex.mm"
include "cdom.mm"
include "wex.mm"
include "cn0.mm"
include "wcel.mm"
include "wceq.mm"
include "adantr.mm"
include "hashfz1.mm"
include "syl.mm"
include "simprl.mm"
include "eqbrtrd.mm"
include "cfn.mm"
include "cvv.mm"
include "wb.mm"
include "fzfid.mm"
include "vex.mm"
include "hashdom.mm"
include "sylancl.mm"
include "mpbid.mm"
include "domen.mm"
include "sylib.mm"
include "cin.mm"
include "cres.mm"
include "simpll.mm"
include "ensym.mm"
include "ad2antrl.mm"
include "hasheni.mm"
include "ad2antrr.mm"
include "eqtrd.mm"
include "simplrr.mm"
include "a1i.mm"
include "simprr.mm"
include "hashbcss.mm"
include "syl3anc.mm"
include "fssresd.mm"
include "wi.mm"
include "resex.mm"
include "feq1.mm"
include "anbi2d.mm"
include "cnveq.mm"
include "imaeq1d.mm"
include "cnvresima.mm"
include "syl6eq.mm"
include "sseq2d.mm"
include "2rexbidv.mm"
include "imbi12d.mm"
include "vtocl.mm"
include "syl12anc.mm"
include "sstr.mm"
include "expcom.mm"
include "ad2antll.mm"
include "selpw.mm"
include "3imtr4g.mm"
include "id.mm"
include "inss1.mm"
include "syl6ss.mm"
include "anim2d.mm"
include "anim12d.mm"
include "reximdv2.mm"
include "reximdv.mm"
include "mpd.mm"
include "exlimddv.mm"
include "ramub.mm"

theorem ramub2
  let wph: wff ph
  let vx: setvar x
  let cC: class C
  let cR: class R
  let vf: setvar f
  let vi: setvar i
  let cF: class F
  let cM: class M
  let cN: class N
  let cV: class V
  let vs: setvar s
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vg: setvar g
  let vn: setvar n
  let vt: setvar t
  let cG: class G
  let cS: class S
  assume rami.c: |- C = ( a e. _V , i e. NN0 |-> { b e. ~P a | ( # ` b ) = i } )
  assume rami.m: |- ( ph -> M e. NN0 )
  assume rami.r: |- ( ph -> R e. V )
  assume rami.f: |- ( ph -> F : R --> NN0 )
  assume ramub2.n: |- ( ph -> N e. NN0 )
  assume ramub2.i: |- ( ( ph /\ ( ( # ` s ) = N /\ f : ( s C M ) --> R ) ) -> E. c e. R E. x e. ~P s ( ( F ` c ) <_ ( # ` x ) /\ ( x C M ) C_ ( `' f " { c } ) ) )

  disjoint c f
  disjoint c s
  disjoint c x
  disjoint C c
  disjoint f s
  disjoint f x
  disjoint C f
  disjoint s x
  disjoint C s
  disjoint C x
  disjoint c ph
  disjoint f ph
  disjoint ph s
  disjoint ph x
  disjoint F c
  disjoint F f
  disjoint F s
  disjoint F x
  disjoint a b
  disjoint a c
  disjoint a f
  disjoint a i
  disjoint a s
  disjoint a x
  disjoint M a
  disjoint b c
  disjoint b f
  disjoint b i
  disjoint b s
  disjoint b x
  disjoint M b
  disjoint c i
  disjoint M c
  disjoint f i
  disjoint M f
  disjoint i s
  disjoint i x
  disjoint M i
  disjoint M s
  disjoint M x
  disjoint R c
  disjoint R f
  disjoint R s
  disjoint R x
  disjoint N a
  disjoint N c
  disjoint N f
  disjoint N i
  disjoint N s
  disjoint N x
  disjoint V c
  disjoint V f
  disjoint V s
  disjoint V x
  disjoint c g
  disjoint c n
  disjoint c t
  disjoint f g
  disjoint f n
  disjoint f t
  disjoint g n
  disjoint g s
  disjoint g t
  disjoint g x
  disjoint C g
  disjoint n s
  disjoint n t
  disjoint n x
  disjoint C n
  disjoint s t
  disjoint t x
  disjoint C t
  disjoint G c
  disjoint G f
  disjoint G x
  disjoint g ph
  disjoint ph t
  disjoint S c
  disjoint S f
  disjoint S s
  disjoint S x
  disjoint F g
  disjoint F n
  disjoint F t
  disjoint a g
  disjoint a n
  disjoint a t
  disjoint b g
  disjoint b n
  disjoint b t
  disjoint g i
  disjoint M g
  disjoint i n
  disjoint i t
  disjoint M n
  disjoint M t
  disjoint R g
  disjoint R n
  disjoint R t
  disjoint N g
  disjoint N n
  disjoint N t
  disjoint V g
  disjoint V n
  disjoint V t
  assert |- ( ph -> ( M Ramsey F ) <_ N )

  proof
    wph
    vx
    cC
    cR
    vg
    vi
    cF
    cM
    cN
    cV
    vt
    va
    vb
    vc
    rami.c
    rami.m
    rami.r
    rami.f
    ramub2.n
    wph
    cN
    vt
    cv
    #
    chash
    cfv
    #
    cle
    wbr
    #
    @0
    cM
    cC
    co
    #
    cR
    vg
    cv
    #
    wf
    #
    wa
    #
    wa
    #
    c1
    cN
    cfz
    co
    #
    vs
    cv
    #
    cen
    wbr
    #
    @9
    @0
    wss
    #
    wa
    #
    vc
    cv
    #
    cF
    cfv
    vx
    cv
    #
    chash
    cfv
    cle
    wbr
    #
    @14
    cM
    cC
    co
    #
    @4
    ccnv
    @13
    csn
    #
    cima
    #
    wss
    #
    wa
    #
    vx
    @0
    cpw
    #
    wrex
    #
    vc
    cR
    wrex
    #
    vs
    @7
    @8
    @0
    cdom
    wbr
    #
    @12
    vs
    wex
    @7
    @8
    chash
    cfv
    #
    @1
    cle
    wbr
    #
    @24
    @7
    @25
    cN
    @1
    cle
    @7
    cN
    cn0
    wcel
    #
    @25
    cN
    wceq
    #
    wph
    @27
    @6
    ramub2.n
    adantr
    cN
    hashfz1
    #
    syl
    wph
    @2
    @5
    simprl
    eqbrtrd
    @7
    @8
    cfn
    wcel
    @0
    cvv
    wcel
    #
    @26
    @24
    wb
    @7
    c1
    cN
    fzfid
    vt
    vex
    #
    @8
    @0
    cvv
    hashdom
    sylancl
    mpbid
    vs
    @8
    @0
    @31
    domen
    sylib
    @7
    @12
    wa
    #
    @15
    @16
    @18
    @9
    cM
    cC
    co
    #
    cin
    #
    wss
    #
    wa
    #
    vx
    @9
    cpw
    #
    wrex
    #
    vc
    cR
    wrex
    #
    @23
    @32
    wph
    @9
    chash
    cfv
    #
    cN
    wceq
    #
    @33
    cR
    @4
    @33
    cres
    #
    wf
    #
    @39
    wph
    @6
    @12
    simpll
    @32
    @40
    @25
    cN
    @32
    @9
    @8
    cen
    wbr
    #
    @40
    @25
    wceq
    @10
    @44
    @7
    @11
    @8
    @9
    ensym
    ad2antrl
    @9
    @8
    hasheni
    syl
    @32
    @27
    @28
    wph
    @27
    @6
    @12
    ramub2.n
    ad2antrr
    @29
    syl
    eqtrd
    @32
    @3
    cR
    @33
    @4
    wph
    @2
    @5
    @12
    simplrr
    @32
    @30
    @11
    cM
    cn0
    wcel
    #
    @33
    @3
    wss
    @30
    @32
    @31
    a1i
    @7
    @10
    @11
    simprr
    wph
    @45
    @6
    @12
    rami.m
    ad2antrr
    @0
    @9
    cC
    vi
    cM
    cvv
    va
    vb
    rami.c
    hashbcss
    syl3anc
    fssresd
    wph
    @41
    @33
    cR
    vf
    cv
    #
    wf
    #
    wa
    #
    wa
    #
    @15
    @16
    @46
    ccnv
    #
    @17
    cima
    #
    wss
    #
    wa
    #
    vx
    @37
    wrex
    vc
    cR
    wrex
    #
    wi
    wph
    @41
    @43
    wa
    #
    wa
    #
    @39
    wi
    vf
    @42
    @4
    @33
    vg
    vex
    resex
    @46
    @42
    wceq
    #
    @49
    @56
    @54
    @39
    @57
    @48
    @55
    wph
    @57
    @47
    @43
    @41
    @33
    cR
    @46
    @42
    feq1
    anbi2d
    anbi2d
    @57
    @53
    @36
    vc
    vx
    cR
    @37
    @57
    @52
    @35
    @15
    @57
    @51
    @34
    @16
    @57
    @51
    @42
    ccnv
    #
    @17
    cima
    @34
    @57
    @50
    @58
    @17
    @46
    @42
    cnveq
    imaeq1d
    @33
    @17
    @4
    cnvresima
    syl6eq
    sseq2d
    anbi2d
    2rexbidv
    imbi12d
    ramub2.i
    vtocl
    syl12anc
    @32
    @38
    @22
    vc
    cR
    @32
    @36
    @20
    vx
    @37
    @21
    @32
    @14
    @37
    wcel
    #
    @14
    @21
    wcel
    #
    @36
    @20
    @32
    @14
    @9
    wss
    #
    @14
    @0
    wss
    #
    @59
    @60
    @11
    @61
    @62
    wi
    @7
    @10
    @61
    @11
    @62
    @14
    @9
    @0
    sstr
    expcom
    ad2antll
    vx
    @9
    selpw
    vx
    @0
    selpw
    3imtr4g
    @32
    @35
    @19
    @15
    @35
    @19
    wi
    @32
    @35
    @16
    @34
    @18
    @35
    id
    @18
    @33
    inss1
    syl6ss
    a1i
    anim2d
    anim12d
    reximdv2
    reximdv
    mpd
    exlimddv
    ramub
end
