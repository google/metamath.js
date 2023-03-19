include "com.mm"
include "cvv.mm"
include "cv.mm"
include "cfv.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cif.mm"
include "cmpt2.mm"
include "crn.mm"
include "cuni.mm"
include "cseqom.mm"
include "cint.mm"
include "wss.mm"
include "crab.mm"
include "cen.mm"
include "wbr.mm"
include "crio.mm"
include "cmpt.mm"
include "cdif.mm"
include "cfn.mm"
include "wcel.mm"
include "ccom.mm"
include "fveq2.mm"
include "ineq1d.mm"
include "eqeq1d.mm"
include "ifbieq2d.mm"
include "ineq2.mm"
include "id.mm"
include "ifbieq12d.mm"
include "cbvmpt2v.mm"
include "eqid.mm"
include "seqomeq12.mm"
include "mp2an.mm"
include "sseq2d.mm"
include "cbvrabv.mm"
include "fin23lem32.mm"

theorem fin23lem33
  let vx: setvar x
  let vf: setvar f
  let vg: setvar g
  let cF: class F
  let cG: class G
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vl: setvar l
  let vy: setvar y
  let cA: class A
  let vh: setvar h
  let cB: class B
  let wph: wff ph
  let cY: class Y
  assume fin23lem33.f: |- F = { g | A. a e. ( ~P g ^m _om ) ( A. x e. _om ( a ` suc x ) C_ ( a ` x ) -> |^| ran a e. ran a ) }

  disjoint a b
  disjoint a f
  disjoint a g
  disjoint a x
  disjoint b f
  disjoint b g
  disjoint b x
  disjoint f g
  disjoint f x
  disjoint g x
  disjoint G a
  disjoint G b
  disjoint G f
  disjoint G g
  disjoint G x
  disjoint F a
  disjoint a c
  disjoint a d
  disjoint a e
  disjoint a i
  disjoint a j
  disjoint a k
  disjoint a l
  disjoint a y
  disjoint b c
  disjoint b d
  disjoint b e
  disjoint b i
  disjoint b j
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
  disjoint f i
  disjoint f j
  disjoint f k
  disjoint f l
  disjoint f y
  disjoint g i
  disjoint g j
  disjoint g k
  disjoint g l
  disjoint g y
  disjoint i j
  disjoint i k
  disjoint i l
  disjoint i x
  disjoint i y
  disjoint j k
  disjoint j l
  disjoint j x
  disjoint j y
  disjoint k l
  disjoint k x
  disjoint k y
  disjoint l x
  disjoint l y
  disjoint x y
  disjoint A a
  disjoint A j
  disjoint a h
  disjoint b h
  disjoint c h
  disjoint G c
  disjoint d h
  disjoint G d
  disjoint e h
  disjoint G e
  disjoint f h
  disjoint g h
  disjoint h i
  disjoint h j
  disjoint h x
  disjoint G h
  disjoint G i
  disjoint G j
  disjoint B a
  disjoint B b
  disjoint F c
  disjoint F e
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint d ph
  disjoint e ph
  disjoint j ph
  disjoint Y a
  disjoint Y b
  disjoint Y c
  disjoint Y d
  disjoint Y e
  disjoint Y j
  assert |- ( G e. F -> E. f A. b ( ( b : _om -1-1-> _V /\ U. ran b C_ G ) -> ( ( f ` b ) : _om -1-1-> _V /\ U. ran ( f ` b ) C. U. ran b ) ) )

  proof
    vx
    vi
    vg
    vy
    vd
    ve
    vj
    vk
    com
    cvv
    vj
    cv
    #
    ve
    cv
    #
    cfv
    #
    vk
    cv
    #
    cin
    #
    c0
    wceq
    #
    @3
    @4
    cif
    #
    cmpt2
    #
    @1
    crn
    cuni
    #
    cseqom
    #
    crn
    cint
    #
    vl
    cv
    #
    @1
    cfv
    #
    wss
    #
    vl
    com
    crab
    #
    vg
    com
    vx
    cv
    #
    @14
    cin
    vg
    cv
    #
    cen
    wbr
    vx
    @14
    crio
    cmpt
    #
    vg
    com
    @15
    com
    @14
    cdif
    #
    cin
    @16
    cen
    wbr
    vx
    @18
    crio
    cmpt
    #
    @9
    vf
    vg
    vc
    cF
    cG
    @14
    cfn
    wcel
    @1
    @19
    ccom
    vi
    @14
    vi
    cv
    @1
    cfv
    @10
    cdif
    cmpt
    @17
    ccom
    cif
    #
    va
    vb
    @7
    vc
    vd
    com
    cvv
    vc
    cv
    #
    @1
    cfv
    #
    vd
    cv
    #
    cin
    #
    c0
    wceq
    #
    @23
    @24
    cif
    #
    cmpt2
    #
    wceq
    @8
    @8
    wceq
    @9
    @27
    @8
    cseqom
    wceq
    vj
    vk
    vc
    vd
    com
    cvv
    @6
    @26
    @22
    @3
    cin
    #
    c0
    wceq
    #
    @3
    @28
    cif
    @0
    @21
    wceq
    #
    @5
    @29
    @4
    @28
    @3
    @30
    @4
    @28
    c0
    @30
    @2
    @22
    @3
    @0
    @21
    @1
    fveq2
    ineq1d
    #
    eqeq1d
    @31
    ifbieq2d
    @3
    @23
    wceq
    #
    @29
    @25
    @3
    @28
    @23
    @24
    @32
    @28
    @24
    c0
    @3
    @23
    @22
    ineq2
    #
    eqeq1d
    @32
    id
    @33
    ifbieq12d
    cbvmpt2v
    @8
    eqid
    @7
    @27
    @8
    @8
    seqomeq12
    mp2an
    fin23lem33.f
    @13
    @10
    vy
    cv
    #
    @1
    cfv
    #
    wss
    vl
    vy
    com
    @11
    @34
    wceq
    @12
    @35
    @10
    @11
    @34
    @1
    fveq2
    sseq2d
    cbvrabv
    @17
    eqid
    @19
    eqid
    @20
    eqid
    fin23lem32
end
