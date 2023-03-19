include "cz.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "crn.mm"
include "wf.mm"
include "cbs.mm"
include "wfun.mm"
include "co.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "fvexd.mm"
include "cgrp.mm"
include "ccyg.mm"
include "cyggrp.mm"
include "syl.mm"
include "adantr.mm"
include "simpr.mm"
include "wceq.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "sseldi.mm"
include "mulgcl.mm"
include "syl3anc.mm"
include "fveq2.mm"
include "oveq1.mm"
include "wi.mm"
include "cygznlem1.mm"
include "biimpd.mm"
include "exp32.mm"
include "3imp2.mm"
include "fliftfund.mm"
include "fliftf.mm"
include "mpbid.mm"
include "wfo.mm"
include "cn0.mm"
include "cfn.mm"
include "chash.mm"
include "cc0.mm"
include "cif.mm"
include "hashcl.mm"
include "adantl.mm"
include "wn.mm"
include "0nn0.mm"
include "a1i.mm"
include "ifclda.mm"
include "syl5eqel.mm"
include "eqid.mm"
include "znzrhfo.mm"
include "fof.mm"
include "feqmptd.mm"
include "rneqd.mm"
include "forn.mm"
include "eqtr3d.mm"
include "feq2d.mm"

theorem cygznlem2a
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let c.x: class .x.
  let vm: setvar m
  let vn: setvar n
  let cE: class E
  let cF: class F
  let cG: class G
  let cL: class L
  let cN: class N
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  let vg: setvar g
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vz: setvar z
  let cM: class M
  assume cygzn.b: |- B = ( Base ` G )
  assume cygzn.n: |- N = if ( B e. Fin , ( # ` B ) , 0 )
  assume cygzn.y: |- Y = ( Z/nZ ` N )
  assume cygzn.m: |- .x. = ( .g ` G )
  assume cygzn.l: |- L = ( ZRHom ` Y )
  assume cygzn.e: |- E = { x e. B | ran ( n e. ZZ |-> ( n .x. x ) ) = B }
  assume cygzn.g: |- ( ph -> G e. CycGrp )
  assume cygzn.x: |- ( ph -> X e. E )
  assume cygzn.f: |- F = ran ( m e. ZZ |-> <. ( L ` m ) , ( m .x. X ) >. )

  disjoint m n
  disjoint m x
  disjoint B m
  disjoint n x
  disjoint B n
  disjoint B x
  disjoint G m
  disjoint G n
  disjoint G x
  disjoint .x. m
  disjoint .x. n
  disjoint .x. x
  disjoint Y m
  disjoint Y n
  disjoint Y x
  disjoint L m
  disjoint L n
  disjoint L x
  disjoint N x
  disjoint m ph
  disjoint F n
  disjoint F x
  disjoint X m
  disjoint X n
  disjoint X x
  disjoint a b
  disjoint a g
  disjoint a i
  disjoint a j
  disjoint a k
  disjoint a m
  disjoint a n
  disjoint a x
  disjoint a z
  disjoint B a
  disjoint b g
  disjoint b i
  disjoint b j
  disjoint b k
  disjoint b m
  disjoint b n
  disjoint b x
  disjoint b z
  disjoint B b
  disjoint g i
  disjoint g j
  disjoint g k
  disjoint g m
  disjoint g n
  disjoint g x
  disjoint g z
  disjoint B g
  disjoint i j
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i x
  disjoint i z
  disjoint B i
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j x
  disjoint j z
  disjoint B j
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k z
  disjoint B k
  disjoint m z
  disjoint n z
  disjoint x z
  disjoint B z
  disjoint E z
  disjoint G a
  disjoint G b
  disjoint G g
  disjoint G i
  disjoint G j
  disjoint G z
  disjoint M m
  disjoint .x. a
  disjoint .x. j
  disjoint .x. k
  disjoint .x. z
  disjoint Y a
  disjoint Y b
  disjoint Y g
  disjoint Y i
  disjoint Y j
  disjoint Y z
  disjoint L a
  disjoint L i
  disjoint L j
  disjoint L k
  disjoint a ph
  disjoint b ph
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint ph z
  disjoint F a
  disjoint F b
  disjoint F i
  disjoint F j
  disjoint F k
  disjoint F z
  disjoint X a
  disjoint X j
  disjoint X k
  disjoint X z
  assert |- ( ph -> F : ( Base ` Y ) --> B )

  proof
    wph
    vm
    cz
    vm
    cv
    #
    cL
    cfv
    #
    cmpt
    #
    crn
    #
    cB
    cF
    wf
    #
    cY
    cbs
    cfv
    #
    cB
    cF
    wf
    wph
    cF
    wfun
    @4
    wph
    vm
    vk
    @1
    @0
    cX
    c.x
    co
    #
    vk
    cv
    #
    cL
    cfv
    #
    @7
    cX
    c.x
    co
    #
    cvv
    cB
    cF
    cz
    cygzn.f
    wph
    @0
    cz
    wcel
    #
    wa
    #
    @0
    cL
    fvexd
    #
    @11
    cG
    cgrp
    wcel
    #
    @10
    cX
    cB
    wcel
    #
    @6
    cB
    wcel
    wph
    @13
    @10
    wph
    cG
    ccyg
    wcel
    @13
    cygzn.g
    cG
    cyggrp
    syl
    adantr
    wph
    @10
    simpr
    wph
    @14
    @10
    wph
    cE
    cB
    cX
    cE
    vn
    cz
    vn
    cv
    vx
    cv
    c.x
    co
    cmpt
    crn
    cB
    wceq
    #
    vx
    cB
    crab
    cB
    cygzn.e
    @15
    vx
    cB
    ssrab2
    eqsstri
    cygzn.x
    sseldi
    adantr
    cB
    c.x
    cG
    @0
    cX
    cygzn.b
    cygzn.m
    mulgcl
    syl3anc
    #
    @0
    @7
    cL
    fveq2
    @0
    @7
    cX
    c.x
    oveq1
    wph
    @10
    @7
    cz
    wcel
    #
    @1
    @8
    wceq
    #
    @6
    @9
    wceq
    #
    wph
    @10
    @17
    @18
    @19
    wi
    wph
    @10
    @17
    wa
    wa
    @18
    @19
    wph
    vx
    cB
    c.x
    vn
    cE
    cG
    @0
    cL
    @7
    cN
    cX
    cY
    cygzn.b
    cygzn.n
    cygzn.y
    cygzn.m
    cygzn.l
    cygzn.e
    cygzn.g
    cygzn.x
    cygznlem1
    biimpd
    exp32
    3imp2
    fliftfund
    wph
    vm
    @1
    @6
    cvv
    cB
    cF
    cz
    cygzn.f
    @12
    @16
    fliftf
    mpbid
    wph
    @3
    @5
    cB
    cF
    wph
    cL
    crn
    #
    @3
    @5
    wph
    cL
    @2
    wph
    vm
    cz
    @5
    cL
    wph
    cz
    @5
    cL
    wfo
    #
    cz
    @5
    cL
    wf
    wph
    cN
    cn0
    wcel
    @21
    wph
    cN
    cB
    cfn
    wcel
    #
    cB
    chash
    cfv
    #
    cc0
    cif
    cn0
    cygzn.n
    wph
    @22
    @23
    cc0
    cn0
    @22
    @23
    cn0
    wcel
    wph
    cB
    hashcl
    adantl
    cc0
    cn0
    wcel
    wph
    @22
    wn
    wa
    0nn0
    a1i
    ifclda
    syl5eqel
    @5
    cL
    cN
    cY
    cygzn.y
    @5
    eqid
    cygzn.l
    znzrhfo
    syl
    #
    cz
    @5
    cL
    fof
    syl
    feqmptd
    rneqd
    wph
    @21
    @20
    @5
    wceq
    @24
    cz
    @5
    cL
    forn
    syl
    eqtr3d
    feq2d
    mpbid
end
