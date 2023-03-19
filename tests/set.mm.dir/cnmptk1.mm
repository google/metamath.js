include "cmpt.mm"
include "ccom.mm"
include "cxko.mm"
include "co.mm"
include "ccn.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wf.mm"
include "wral.mm"
include "ctopon.mm"
include "cfv.mm"
include "adantr.mm"
include "ctop.mm"
include "topontop.mm"
include "syl.mm"
include "eqid.mm"
include "xkotopon.mm"
include "syl2anc.mm"
include "cnf2.mm"
include "syl3anc.mm"
include "fmpt.mm"
include "sylibr.mm"
include "r19.21bi.mm"
include "eqidd.mm"
include "fmptcof.mm"
include "mpteq2dva.mm"
include "xkoco2cn.mm"
include "coeq2.mm"
include "cnmpt11.mm"
include "eqeltrrd.mm"

theorem cnmptk1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cJ: class J
  let cK: class K
  let cL: class L
  let cM: class M
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vw: setvar w
  assume cnmptk1.j: |- ( ph -> J e. ( TopOn ` X ) )
  assume cnmptk1.k: |- ( ph -> K e. ( TopOn ` Y ) )
  assume cnmptk1.l: |- ( ph -> L e. ( TopOn ` Z ) )
  assume cnmptk1.a: |- ( ph -> ( x e. X |-> ( y e. Y |-> A ) ) e. ( J Cn ( L ^ko K ) ) )
  assume cnmptk1.b: |- ( ph -> ( z e. Z |-> B ) e. ( L Cn M ) )
  assume cnmptk1.c: |- ( z = A -> B = C )

  disjoint B y
  disjoint x y
  disjoint J x
  disjoint J y
  disjoint K x
  disjoint K y
  disjoint L x
  disjoint L y
  disjoint M x
  disjoint M y
  disjoint x z
  disjoint Z x
  disjoint y z
  disjoint Z y
  disjoint Z z
  disjoint A z
  disjoint B x
  disjoint ph x
  disjoint ph y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint C z
  disjoint w x
  disjoint w y
  disjoint J w
  disjoint K w
  disjoint L w
  disjoint M w
  disjoint w z
  disjoint Z w
  disjoint A w
  disjoint B w
  disjoint ph w
  disjoint X w
  disjoint Y w
  assert |- ( ph -> ( x e. X |-> ( y e. Y |-> C ) ) e. ( J Cn ( M ^ko K ) ) )

  proof
    wph
    vx
    cX
    vz
    cZ
    cB
    cmpt
    #
    vy
    cY
    cA
    cmpt
    #
    ccom
    #
    cmpt
    vx
    cX
    vy
    cY
    cC
    cmpt
    #
    cmpt
    cJ
    cM
    cK
    cxko
    co
    #
    ccn
    co
    wph
    vx
    cX
    @2
    @3
    wph
    vx
    cv
    cX
    wcel
    #
    wa
    #
    vy
    vz
    cY
    cZ
    cA
    cB
    cC
    @1
    @0
    @6
    cY
    cZ
    @1
    wf
    #
    cA
    cZ
    wcel
    vy
    cY
    wral
    @6
    cK
    cY
    ctopon
    cfv
    wcel
    #
    cL
    cZ
    ctopon
    cfv
    wcel
    #
    @1
    cK
    cL
    ccn
    co
    #
    wcel
    #
    @7
    wph
    @8
    @5
    cnmptk1.k
    adantr
    wph
    @9
    @5
    cnmptk1.l
    adantr
    wph
    @11
    vx
    cX
    wph
    cX
    @10
    vx
    cX
    @1
    cmpt
    #
    wf
    #
    @11
    vx
    cX
    wral
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    cL
    cK
    cxko
    co
    #
    @10
    ctopon
    cfv
    wcel
    #
    @12
    cJ
    @14
    ccn
    co
    wcel
    @13
    cnmptk1.j
    wph
    cK
    ctop
    wcel
    #
    cL
    ctop
    wcel
    #
    @15
    wph
    @8
    @16
    cnmptk1.k
    cY
    cK
    topontop
    syl
    #
    wph
    @9
    @17
    cnmptk1.l
    cZ
    cL
    topontop
    syl
    cK
    cL
    @14
    @14
    eqid
    xkotopon
    syl2anc
    #
    cnmptk1.a
    @12
    cJ
    @14
    cX
    @10
    cnf2
    syl3anc
    vx
    cX
    @10
    @1
    @12
    @12
    eqid
    fmpt
    sylibr
    r19.21bi
    @1
    cK
    cL
    cY
    cZ
    cnf2
    syl3anc
    vy
    cY
    cZ
    cA
    @1
    @1
    eqid
    fmpt
    sylibr
    @6
    @1
    eqidd
    @6
    @0
    eqidd
    cnmptk1.c
    fmptcof
    mpteq2dva
    wph
    vx
    vw
    @1
    @0
    vw
    cv
    #
    ccom
    @2
    cJ
    @14
    @4
    cX
    @10
    cnmptk1.j
    cnmptk1.a
    @19
    wph
    cK
    cL
    cM
    vw
    @0
    @18
    cnmptk1.b
    xkoco2cn
    @20
    @1
    @0
    coeq2
    cnmpt11
    eqeltrrd
end
