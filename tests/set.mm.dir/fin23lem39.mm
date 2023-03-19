include "wcel.mm"
include "com.mm"
include "cv.mm"
include "cfv.mm"
include "crn.mm"
include "cuni.mm"
include "cmpt.mm"
include "cint.mm"
include "fin23lem38.mm"
include "wa.mm"
include "cpw.mm"
include "cmap.mm"
include "co.mm"
include "csuc.mm"
include "wss.mm"
include "wral.mm"
include "wi.mm"
include "wf.mm"
include "cvv.mm"
include "wf1.mm"
include "fin23lem34.mm"
include "simprd.mm"
include "adantlr.mm"
include "wb.mm"
include "elpw2g.mm"
include "ad2antlr.mm"
include "mpbird.mm"
include "eqid.mm"
include "fmptd.mm"
include "pwexg.mm"
include "vex.mm"
include "f1f.mm"
include "dmfex.mm"
include "sylancr.mm"
include "syl.mm"
include "elmapg.mm"
include "syl2anr.mm"
include "isfin3ds.mm"
include "ibi.mm"
include "adantl.mm"
include "fin23lem35.mm"
include "pssssd.mm"
include "wceq.mm"
include "peano2.mm"
include "fveq2.mm"
include "rneqd.mm"
include "unieqd.mm"
include "fvex.mm"
include "rnex.mm"
include "uniex.mm"
include "fvmpt.mm"
include "sseq12d.mm"
include "ralrimiva.mm"
include "adantr.mm"
include "fveq1.mm"
include "ralbidv.mm"
include "rneq.mm"
include "inteqd.mm"
include "eleq12d.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl3c.mm"
include "mtand.mm"

theorem fin23lem39
  let wph: wff ph
  let vx: setvar x
  let vg: setvar g
  let vh: setvar h
  let vi: setvar i
  let vj: setvar j
  let cF: class F
  let cG: class G
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let vk: setvar k
  let vl: setvar l
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume fin23lem33.f: |- F = { g | A. a e. ( ~P g ^m _om ) ( A. x e. _om ( a ` suc x ) C_ ( a ` x ) -> |^| ran a e. ran a ) }
  assume fin23lem.f: |- ( ph -> h : _om -1-1-> _V )
  assume fin23lem.g: |- ( ph -> U. ran h C_ G )
  assume fin23lem.h: |- ( ph -> A. j ( ( j : _om -1-1-> _V /\ U. ran j C_ G ) -> ( ( i ` j ) : _om -1-1-> _V /\ U. ran ( i ` j ) C. U. ran j ) ) )
  assume fin23lem.i: |- Y = ( rec ( i , h ) |` _om )

  disjoint a g
  disjoint a i
  disjoint a j
  disjoint a x
  disjoint g i
  disjoint g j
  disjoint g x
  disjoint i j
  disjoint i x
  disjoint j x
  disjoint a h
  disjoint G a
  disjoint g h
  disjoint G g
  disjoint h i
  disjoint h j
  disjoint h x
  disjoint G h
  disjoint G i
  disjoint G j
  disjoint G x
  disjoint F a
  disjoint a ph
  disjoint j ph
  disjoint Y a
  disjoint Y j
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a e
  disjoint a f
  disjoint a k
  disjoint a l
  disjoint a y
  disjoint b c
  disjoint b d
  disjoint b e
  disjoint b f
  disjoint b g
  disjoint b i
  disjoint b j
  disjoint b k
  disjoint b l
  disjoint b x
  disjoint b y
  disjoint c d
  disjoint c e
  disjoint c f
  disjoint c g
  disjoint c i
  disjoint c j
  disjoint c k
  disjoint c l
  disjoint c x
  disjoint c y
  disjoint d e
  disjoint d f
  disjoint d g
  disjoint d i
  disjoint d j
  disjoint d k
  disjoint d l
  disjoint d x
  disjoint d y
  disjoint e f
  disjoint e g
  disjoint e i
  disjoint e j
  disjoint e k
  disjoint e l
  disjoint e x
  disjoint e y
  disjoint f g
  disjoint f i
  disjoint f j
  disjoint f k
  disjoint f l
  disjoint f x
  disjoint f y
  disjoint g k
  disjoint g l
  disjoint g y
  disjoint i k
  disjoint i l
  disjoint i y
  disjoint j k
  disjoint j l
  disjoint j y
  disjoint k l
  disjoint k x
  disjoint k y
  disjoint l x
  disjoint l y
  disjoint x y
  disjoint A a
  disjoint A j
  disjoint b h
  disjoint G b
  disjoint c h
  disjoint G c
  disjoint d h
  disjoint G d
  disjoint e h
  disjoint G e
  disjoint f h
  disjoint G f
  disjoint B a
  disjoint B b
  disjoint F c
  disjoint F e
  disjoint b ph
  disjoint c ph
  disjoint d ph
  disjoint e ph
  disjoint Y b
  disjoint Y c
  disjoint Y d
  disjoint Y e
  assert |- ( ph -> -. G e. F )

  proof
    wph
    cG
    cF
    wcel
    #
    vc
    com
    vc
    cv
    #
    cY
    cfv
    #
    crn
    #
    cuni
    #
    cmpt
    #
    crn
    #
    cint
    #
    @6
    wcel
    #
    wph
    vx
    vg
    vh
    vi
    vj
    cF
    cG
    cY
    va
    vc
    fin23lem33.f
    fin23lem.f
    fin23lem.g
    fin23lem.h
    fin23lem.i
    fin23lem38
    wph
    @0
    wa
    #
    @5
    cG
    cpw
    #
    com
    cmap
    co
    #
    wcel
    #
    ve
    cv
    #
    csuc
    #
    vd
    cv
    #
    cfv
    #
    @13
    @15
    cfv
    #
    wss
    #
    ve
    com
    wral
    #
    @15
    crn
    #
    cint
    #
    @20
    wcel
    #
    wi
    #
    vd
    @11
    wral
    #
    @14
    @5
    cfv
    #
    @13
    @5
    cfv
    #
    wss
    #
    ve
    com
    wral
    #
    @8
    @9
    @12
    com
    @10
    @5
    wf
    #
    @9
    vc
    com
    @4
    @10
    @5
    @9
    @1
    com
    wcel
    #
    wa
    @4
    @10
    wcel
    #
    @4
    cG
    wss
    #
    wph
    @30
    @32
    @0
    wph
    @30
    wa
    com
    cvv
    @2
    wf1
    @32
    wph
    vx
    @1
    vg
    vh
    vi
    vj
    cF
    cG
    cY
    va
    fin23lem33.f
    fin23lem.f
    fin23lem.g
    fin23lem.h
    fin23lem.i
    fin23lem34
    simprd
    adantlr
    @0
    @31
    @32
    wb
    wph
    @30
    @4
    cG
    cF
    elpw2g
    ad2antlr
    mpbird
    @5
    eqid
    #
    fmptd
    @0
    @10
    cvv
    wcel
    com
    cvv
    wcel
    #
    @12
    @29
    wb
    wph
    cG
    cF
    pwexg
    wph
    com
    cvv
    vh
    cv
    #
    wf1
    #
    @34
    fin23lem.f
    @36
    @35
    cvv
    wcel
    com
    cvv
    @35
    wf
    @34
    vh
    vex
    com
    cvv
    @35
    f1f
    com
    cvv
    cvv
    @35
    dmfex
    sylancr
    syl
    @10
    com
    @5
    cvv
    cvv
    elmapg
    syl2anr
    mpbird
    @0
    @24
    wph
    @0
    @24
    ve
    cG
    vd
    vg
    cF
    cF
    va
    vx
    fin23lem33.f
    isfin3ds
    ibi
    adantl
    wph
    @28
    @0
    wph
    @27
    ve
    com
    wph
    @13
    com
    wcel
    #
    wa
    #
    @27
    @14
    cY
    cfv
    #
    crn
    #
    cuni
    #
    @13
    cY
    cfv
    #
    crn
    #
    cuni
    #
    wss
    #
    @38
    @41
    @44
    wph
    vx
    @13
    vg
    vh
    vi
    vj
    cF
    cG
    cY
    va
    fin23lem33.f
    fin23lem.f
    fin23lem.g
    fin23lem.h
    fin23lem.i
    fin23lem35
    pssssd
    @37
    @27
    @45
    wb
    wph
    @37
    @25
    @41
    @26
    @44
    @37
    @14
    com
    wcel
    @25
    @41
    wceq
    @13
    peano2
    vc
    @14
    @4
    @41
    com
    @5
    @1
    @14
    wceq
    #
    @3
    @40
    @46
    @2
    @39
    @1
    @14
    cY
    fveq2
    rneqd
    unieqd
    @33
    @40
    @39
    @14
    cY
    fvex
    rnex
    uniex
    fvmpt
    syl
    vc
    @13
    @4
    @44
    com
    @5
    @1
    @13
    wceq
    #
    @3
    @43
    @47
    @2
    @42
    @1
    @13
    cY
    fveq2
    rneqd
    unieqd
    @33
    @43
    @42
    @13
    cY
    fvex
    rnex
    uniex
    fvmpt
    sseq12d
    adantl
    mpbird
    ralrimiva
    adantr
    @23
    @28
    @8
    wi
    vd
    @5
    @11
    @15
    @5
    wceq
    #
    @19
    @28
    @22
    @8
    @48
    @18
    @27
    ve
    com
    @48
    @16
    @25
    @17
    @26
    @14
    @15
    @5
    fveq1
    @13
    @15
    @5
    fveq1
    sseq12d
    ralbidv
    @48
    @21
    @7
    @20
    @6
    @48
    @20
    @6
    @15
    @5
    rneq
    #
    inteqd
    @49
    eleq12d
    imbi12d
    rspcv
    syl3c
    mtand
end
