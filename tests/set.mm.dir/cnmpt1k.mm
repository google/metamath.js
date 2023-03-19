include "cmpt.mm"
include "ccom.mm"
include "cxko.mm"
include "co.mm"
include "ccn.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wral.mm"
include "wf.mm"
include "ctopon.mm"
include "cfv.mm"
include "cnf2.mm"
include "syl3anc.mm"
include "eqid.mm"
include "fmpt.mm"
include "sylibr.mm"
include "adantr.mm"
include "eqidd.mm"
include "fmptcof.mm"
include "mpteq2dva.mm"
include "ctop.mm"
include "topontop.mm"
include "syl.mm"
include "xkotopon.mm"
include "syl2anc.mm"
include "xkoco1cn.mm"
include "coeq1.mm"
include "cnmpt11.mm"
include "eqeltrrd.mm"

theorem cnmpt1k
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
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vw: setvar w
  assume cnmptk1.j: |- ( ph -> J e. ( TopOn ` X ) )
  assume cnmptk1.k: |- ( ph -> K e. ( TopOn ` Y ) )
  assume cnmptk1.l: |- ( ph -> L e. ( TopOn ` Z ) )
  assume cnmpt1k.m: |- ( ph -> M e. ( TopOn ` W ) )
  assume cnmpt1k.a: |- ( ph -> ( x e. X |-> A ) e. ( J Cn L ) )
  assume cnmpt1k.b: |- ( ph -> ( y e. Y |-> ( z e. Z |-> B ) ) e. ( K Cn ( M ^ko L ) ) )
  assume cnmpt1k.c: |- ( z = A -> B = C )

  disjoint A y
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
  assert |- ( ph -> ( y e. Y |-> ( x e. X |-> C ) ) e. ( K Cn ( M ^ko J ) ) )

  proof
    wph
    vy
    cY
    vz
    cZ
    cB
    cmpt
    #
    vx
    cX
    cA
    cmpt
    #
    ccom
    #
    cmpt
    vy
    cY
    vx
    cX
    cC
    cmpt
    #
    cmpt
    cK
    cM
    cJ
    cxko
    co
    #
    ccn
    co
    wph
    vy
    cY
    @2
    @3
    wph
    vy
    cv
    cY
    wcel
    #
    wa
    #
    vx
    vz
    cX
    cZ
    cA
    cB
    cC
    @1
    @0
    wph
    cA
    cZ
    wcel
    vx
    cX
    wral
    #
    @5
    wph
    cX
    cZ
    @1
    wf
    #
    @7
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    cL
    cZ
    ctopon
    cfv
    wcel
    #
    @1
    cJ
    cL
    ccn
    co
    wcel
    @8
    cnmptk1.j
    cnmptk1.l
    cnmpt1k.a
    @1
    cJ
    cL
    cX
    cZ
    cnf2
    syl3anc
    vx
    cX
    cZ
    cA
    @1
    @1
    eqid
    fmpt
    sylibr
    adantr
    @6
    @1
    eqidd
    @6
    @0
    eqidd
    cnmpt1k.c
    fmptcof
    mpteq2dva
    wph
    vy
    vw
    @0
    vw
    cv
    #
    @1
    ccom
    @2
    cK
    cM
    cL
    cxko
    co
    #
    @4
    cY
    cL
    cM
    ccn
    co
    #
    cnmptk1.k
    cnmpt1k.b
    wph
    cL
    ctop
    wcel
    #
    cM
    ctop
    wcel
    #
    @11
    @12
    ctopon
    cfv
    wcel
    wph
    @9
    @13
    cnmptk1.l
    cZ
    cL
    topontop
    syl
    wph
    cM
    cW
    ctopon
    cfv
    wcel
    @14
    cnmpt1k.m
    cW
    cM
    topontop
    syl
    #
    cL
    cM
    @11
    @11
    eqid
    xkotopon
    syl2anc
    wph
    cJ
    cL
    cM
    vw
    @1
    @15
    cnmpt1k.a
    xkoco1cn
    @10
    @0
    @1
    coeq1
    cnmpt11
    eqeltrrd
end
