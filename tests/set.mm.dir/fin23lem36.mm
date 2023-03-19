include "com.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "cfv.mm"
include "crn.mm"
include "cuni.mm"
include "cv.mm"
include "wi.mm"
include "csuc.mm"
include "wceq.mm"
include "fveq2.mm"
include "rneqd.mm"
include "unieqd.mm"
include "sseq1d.mm"
include "imbi2d.mm"
include "ssid.mm"
include "2a1i.mm"
include "wpss.mm"
include "simprr.mm"
include "simpll.mm"
include "fin23lem35.mm"
include "syl2anc.mm"
include "pssssd.mm"
include "sstr2.mm"
include "syl.mm"
include "expr.mm"
include "a2d.mm"
include "findsg.mm"
include "impr.mm"

theorem fin23lem36
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
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
  disjoint A a
  disjoint A j
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
  disjoint B a
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
  assert |- ( ( ( A e. _om /\ B e. _om ) /\ ( B C_ A /\ ph ) ) -> U. ran ( Y ` A ) C_ U. ran ( Y ` B ) )

  proof
    cA
    com
    wcel
    cB
    com
    wcel
    #
    wa
    cB
    cA
    wss
    wph
    cA
    cY
    cfv
    #
    crn
    #
    cuni
    #
    cB
    cY
    cfv
    #
    crn
    #
    cuni
    #
    wss
    #
    wph
    va
    cv
    #
    cY
    cfv
    #
    crn
    #
    cuni
    #
    @6
    wss
    #
    wi
    wph
    @6
    @6
    wss
    #
    wi
    wph
    vb
    cv
    #
    cY
    cfv
    #
    crn
    #
    cuni
    #
    @6
    wss
    #
    wi
    wph
    @14
    csuc
    #
    cY
    cfv
    #
    crn
    #
    cuni
    #
    @6
    wss
    #
    wi
    wph
    @7
    wi
    va
    vb
    cA
    cB
    @8
    cB
    wceq
    #
    @12
    @13
    wph
    @24
    @11
    @6
    @6
    @24
    @10
    @5
    @24
    @9
    @4
    @8
    cB
    cY
    fveq2
    rneqd
    unieqd
    sseq1d
    imbi2d
    @8
    @14
    wceq
    #
    @12
    @18
    wph
    @25
    @11
    @17
    @6
    @25
    @10
    @16
    @25
    @9
    @15
    @8
    @14
    cY
    fveq2
    rneqd
    unieqd
    sseq1d
    imbi2d
    @8
    @19
    wceq
    #
    @12
    @23
    wph
    @26
    @11
    @22
    @6
    @26
    @10
    @21
    @26
    @9
    @20
    @8
    @19
    cY
    fveq2
    rneqd
    unieqd
    sseq1d
    imbi2d
    @8
    cA
    wceq
    #
    @12
    @7
    wph
    @27
    @11
    @3
    @6
    @27
    @10
    @2
    @27
    @9
    @1
    @8
    cA
    cY
    fveq2
    rneqd
    unieqd
    sseq1d
    imbi2d
    @13
    @0
    wph
    @6
    ssid
    2a1i
    @14
    com
    wcel
    #
    @0
    wa
    #
    cB
    @14
    wss
    #
    wa
    wph
    @18
    @23
    @29
    @30
    wph
    @18
    @23
    wi
    #
    @29
    @30
    wph
    wa
    #
    wa
    #
    @22
    @17
    wss
    @31
    @33
    @22
    @17
    @33
    wph
    @28
    @22
    @17
    wpss
    @29
    @30
    wph
    simprr
    @28
    @0
    @32
    simpll
    wph
    vx
    @14
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
    syl2anc
    pssssd
    @22
    @17
    @6
    sstr2
    syl
    expr
    a2d
    findsg
    impr
end
