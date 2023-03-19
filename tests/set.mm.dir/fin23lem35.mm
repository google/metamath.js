include "com.mm"
include "wcel.mm"
include "wa.mm"
include "csuc.mm"
include "cfv.mm"
include "crn.mm"
include "cuni.mm"
include "wpss.mm"
include "cv.mm"
include "cvv.mm"
include "wf1.mm"
include "wss.mm"
include "fin23lem34.mm"
include "wi.mm"
include "wal.mm"
include "fvex.mm"
include "wceq.mm"
include "f1eq1.mm"
include "rneq.mm"
include "unieqd.mm"
include "sseq1d.mm"
include "anbi12d.mm"
include "wb.mm"
include "fveq2.mm"
include "syl.mm"
include "rneqd.mm"
include "psseq12d.mm"
include "imbi12d.mm"
include "spcv.mm"
include "adantr.mm"
include "mpd.mm"
include "simprd.mm"
include "crdg.mm"
include "cres.mm"
include "frsuc.mm"
include "adantl.mm"
include "fveq1i.mm"
include "fveq2i.mm"
include "3eqtr4g.mm"
include "psseq1d.mm"
include "mpbird.mm"

theorem fin23lem35
  let wph: wff ph
  let vx: setvar x
  let cA: class A
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
  assert |- ( ( ph /\ A e. _om ) -> U. ran ( Y ` suc A ) C. U. ran ( Y ` A ) )

  proof
    wph
    cA
    com
    wcel
    #
    wa
    #
    cA
    csuc
    #
    cY
    cfv
    #
    crn
    #
    cuni
    #
    cA
    cY
    cfv
    #
    crn
    #
    cuni
    #
    wpss
    @6
    vi
    cv
    #
    cfv
    #
    crn
    #
    cuni
    #
    @8
    wpss
    #
    @1
    com
    cvv
    @10
    wf1
    #
    @13
    @1
    com
    cvv
    @6
    wf1
    #
    @8
    cG
    wss
    #
    wa
    #
    @14
    @13
    wa
    #
    wph
    vx
    cA
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
    wph
    @17
    @18
    wi
    #
    @0
    wph
    com
    cvv
    vj
    cv
    #
    wf1
    #
    @20
    crn
    #
    cuni
    #
    cG
    wss
    #
    wa
    #
    com
    cvv
    @20
    @9
    cfv
    #
    wf1
    #
    @26
    crn
    #
    cuni
    #
    @23
    wpss
    #
    wa
    #
    wi
    #
    vj
    wal
    @19
    fin23lem.h
    @32
    @19
    vj
    @6
    cA
    cY
    fvex
    @20
    @6
    wceq
    #
    @25
    @17
    @31
    @18
    @33
    @21
    @15
    @24
    @16
    com
    cvv
    @20
    @6
    f1eq1
    @33
    @23
    @8
    cG
    @33
    @22
    @7
    @20
    @6
    rneq
    unieqd
    #
    sseq1d
    anbi12d
    @33
    @27
    @14
    @30
    @13
    @33
    @26
    @10
    wceq
    @27
    @14
    wb
    @20
    @6
    @9
    fveq2
    #
    com
    cvv
    @26
    @10
    f1eq1
    syl
    @33
    @29
    @12
    @23
    @8
    @33
    @28
    @11
    @33
    @26
    @10
    @35
    rneqd
    unieqd
    @34
    psseq12d
    anbi12d
    imbi12d
    spcv
    syl
    adantr
    mpd
    simprd
    @1
    @5
    @12
    @8
    @1
    @4
    @11
    @1
    @3
    @10
    @1
    @2
    @9
    vh
    cv
    #
    crdg
    com
    cres
    #
    cfv
    #
    cA
    @37
    cfv
    #
    @9
    cfv
    #
    @3
    @10
    @0
    @38
    @40
    wceq
    wph
    @36
    cA
    @9
    frsuc
    adantl
    @2
    cY
    @37
    fin23lem.i
    fveq1i
    @6
    @39
    @9
    cA
    cY
    @37
    fin23lem.i
    fveq1i
    fveq2i
    3eqtr4g
    rneqd
    unieqd
    psseq1d
    mpbird
end
