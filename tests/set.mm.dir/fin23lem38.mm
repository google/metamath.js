include "com.mm"
include "cv.mm"
include "cfv.mm"
include "crn.mm"
include "cuni.mm"
include "cmpt.mm"
include "cint.mm"
include "wceq.mm"
include "wrex.mm"
include "wcel.mm"
include "wa.mm"
include "wpss.mm"
include "wn.mm"
include "csuc.mm"
include "wss.mm"
include "peano2.mm"
include "eqid.mm"
include "fveq2.mm"
include "rneqd.mm"
include "unieqd.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "mpan2.mm"
include "cvv.mm"
include "wb.mm"
include "fvex.mm"
include "rnex.mm"
include "uniex.mm"
include "elrnmpt.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "syl.mm"
include "adantl.mm"
include "intss1.mm"
include "fin23lem35.mm"
include "sspsstrd.mm"
include "dfpss2.mm"
include "simprbi.mm"
include "nrexdv.mm"
include "cbvmptv.mm"
include "ibi.mm"
include "nsyl.mm"

theorem fin23lem38
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

  disjoint a b
  disjoint a g
  disjoint a i
  disjoint a j
  disjoint a x
  disjoint b g
  disjoint b i
  disjoint b j
  disjoint b x
  disjoint g i
  disjoint g j
  disjoint g x
  disjoint i j
  disjoint i x
  disjoint j x
  disjoint a h
  disjoint G a
  disjoint b h
  disjoint G b
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
  disjoint b ph
  disjoint j ph
  disjoint Y a
  disjoint Y b
  disjoint Y j
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
  disjoint b k
  disjoint b l
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
  disjoint c ph
  disjoint d ph
  disjoint e ph
  disjoint Y c
  disjoint Y d
  disjoint Y e
  assert |- ( ph -> -. |^| ran ( b e. _om |-> U. ran ( Y ` b ) ) e. ran ( b e. _om |-> U. ran ( Y ` b ) ) )

  proof
    wph
    vb
    com
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
    cmpt
    #
    crn
    #
    cint
    #
    vd
    cv
    #
    cY
    cfv
    #
    crn
    #
    cuni
    #
    wceq
    #
    vd
    com
    wrex
    #
    @6
    @5
    wcel
    #
    wph
    @11
    vd
    com
    wph
    @7
    com
    wcel
    #
    wa
    #
    @6
    @10
    wpss
    #
    @11
    wn
    #
    @15
    @6
    @7
    csuc
    #
    cY
    cfv
    #
    crn
    #
    cuni
    #
    @10
    @15
    @21
    @5
    wcel
    #
    @6
    @21
    wss
    @14
    @22
    wph
    @14
    @18
    com
    wcel
    #
    @22
    @7
    peano2
    @23
    @21
    @3
    wceq
    #
    vb
    com
    wrex
    #
    @22
    @23
    @21
    @21
    wceq
    #
    @25
    @21
    eqid
    @24
    @26
    vb
    @18
    com
    @0
    @18
    wceq
    #
    @3
    @21
    @21
    @27
    @2
    @20
    @27
    @1
    @19
    @0
    @18
    cY
    fveq2
    rneqd
    unieqd
    eqeq2d
    rspcev
    mpan2
    @21
    cvv
    wcel
    @22
    @25
    wb
    @20
    @19
    @18
    cY
    fvex
    rnex
    uniex
    vb
    com
    @3
    @21
    @4
    cvv
    @4
    eqid
    elrnmpt
    ax-mp
    sylibr
    syl
    adantl
    @21
    @5
    intss1
    syl
    wph
    vx
    @7
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
    sspsstrd
    @16
    @6
    @10
    wss
    @17
    @6
    @10
    dfpss2
    simprbi
    syl
    nrexdv
    @13
    @12
    vd
    com
    @10
    @6
    @4
    @5
    vb
    vd
    com
    @3
    @10
    @0
    @7
    wceq
    #
    @2
    @9
    @28
    @1
    @8
    @0
    @7
    cY
    fveq2
    rneqd
    unieqd
    cbvmptv
    elrnmpt
    ibi
    nsyl
end
