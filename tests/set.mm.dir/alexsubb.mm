include "cufl.mm"
include "wcel.mm"
include "cuni.mm"
include "wceq.mm"
include "wa.mm"
include "cfi.mm"
include "cfv.mm"
include "ctg.mm"
include "ccmp.mm"
include "cv.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "ctop.mm"
include "eqid.mm"
include "iscmp.mm"
include "simprbi.mm"
include "cvv.mm"
include "simpr.mm"
include "elex.mm"
include "adantr.mm"
include "eqeltrrd.mm"
include "uniexb.mm"
include "sylibr.mm"
include "fiuni.mm"
include "syl.mm"
include "ctb.mm"
include "fibas.mm"
include "unitg.mm"
include "mp1i.mm"
include "3eqtr4d.mm"
include "eqeq1d.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "ralbidv.mm"
include "wss.mm"
include "ssfii.mm"
include "bastg.mm"
include "ax-mp.mm"
include "syl6ss.mm"
include "sspwb.mm"
include "sylib.mm"
include "ssralv.mm"
include "sylbird.mm"
include "syl5.mm"
include "simpll.mm"
include "simplr.mm"
include "eqidd.mm"
include "selpw.mm"
include "unieq.mm"
include "eqeq2d.mm"
include "pweq.mm"
include "ineq1d.mm"
include "rexeqdv.mm"
include "rspccv.mm"
include "adantl.mm"
include "syl5bir.mm"
include "imp32.mm"
include "cbvrexv.mm"
include "alexsub.mm"
include "ex.mm"
include "impbid.mm"

theorem alexsubb
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cX: class X
  let vw: setvar w
  let vz: setvar z

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint X x
  disjoint X y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint x z
  disjoint y z
  disjoint B z
  disjoint X w
  disjoint X z
  assert |- ( ( X e. UFL /\ X = U. B ) -> ( ( topGen ` ( fi ` B ) ) e. Comp <-> A. x e. ~P B ( X = U. x -> E. y e. ( ~P x i^i Fin ) X = U. y ) ) )

  proof
    cX
    cufl
    wcel
    #
    cX
    cB
    cuni
    #
    wceq
    #
    wa
    #
    cB
    cfi
    cfv
    #
    ctg
    cfv
    #
    ccmp
    wcel
    #
    cX
    vx
    cv
    #
    cuni
    #
    wceq
    #
    cX
    vy
    cv
    #
    cuni
    #
    wceq
    #
    vy
    @7
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    wi
    #
    vx
    cB
    cpw
    #
    wral
    #
    @6
    @5
    cuni
    #
    @8
    wceq
    #
    @19
    @11
    wceq
    #
    vy
    @14
    wrex
    #
    wi
    #
    vx
    @5
    cpw
    #
    wral
    #
    @3
    @18
    @6
    @5
    ctop
    wcel
    @25
    vx
    vy
    @5
    @19
    @19
    eqid
    iscmp
    simprbi
    @3
    @25
    @16
    vx
    @24
    wral
    #
    @18
    @3
    @16
    @23
    vx
    @24
    @3
    @9
    @20
    @15
    @22
    @3
    cX
    @19
    @8
    @3
    @1
    @4
    cuni
    #
    cX
    @19
    @3
    cB
    cvv
    wcel
    #
    @1
    @27
    wceq
    @3
    @1
    cvv
    wcel
    @28
    @3
    cX
    @1
    cvv
    @0
    @2
    simpr
    #
    @0
    cX
    cvv
    wcel
    @2
    cX
    cufl
    elex
    adantr
    eqeltrrd
    cB
    uniexb
    sylibr
    #
    cB
    cvv
    fiuni
    syl
    @29
    @4
    ctb
    wcel
    #
    @19
    @27
    wceq
    @3
    cB
    fibas
    #
    @4
    ctb
    unitg
    mp1i
    3eqtr4d
    #
    eqeq1d
    @3
    @12
    @21
    vy
    @14
    @3
    cX
    @19
    @11
    @33
    eqeq1d
    rexbidv
    imbi12d
    ralbidv
    @3
    @17
    @24
    wss
    #
    @26
    @18
    wi
    @3
    cB
    @5
    wss
    @34
    @3
    cB
    @4
    @5
    @3
    @28
    cB
    @4
    wss
    @30
    cB
    cvv
    ssfii
    syl
    @31
    @4
    @5
    wss
    @32
    @4
    ctb
    bastg
    ax-mp
    syl6ss
    cB
    @5
    sspwb
    sylib
    @16
    vx
    @17
    @24
    ssralv
    syl
    sylbird
    syl5
    @3
    @18
    @6
    @3
    @18
    wa
    #
    vz
    vw
    cB
    @5
    cX
    @0
    @2
    @18
    simpll
    @0
    @2
    @18
    simplr
    @35
    @5
    eqidd
    @35
    vz
    cv
    #
    cB
    wss
    #
    cX
    @36
    cuni
    #
    wceq
    #
    wa
    wa
    @12
    vy
    @36
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    cX
    vw
    cv
    #
    cuni
    #
    wceq
    #
    vw
    @41
    wrex
    @35
    @37
    @39
    @42
    @37
    @36
    @17
    wcel
    #
    @35
    @39
    @42
    wi
    #
    vz
    cB
    selpw
    @18
    @46
    @47
    wi
    @3
    @16
    @47
    vx
    @36
    @17
    @7
    @36
    wceq
    #
    @9
    @39
    @15
    @42
    @48
    @8
    @38
    cX
    @7
    @36
    unieq
    eqeq2d
    @48
    @12
    vy
    @14
    @41
    @48
    @13
    @40
    cfn
    @7
    @36
    pweq
    ineq1d
    rexeqdv
    imbi12d
    rspccv
    adantl
    syl5bir
    imp32
    @12
    @45
    vy
    vw
    @41
    @10
    @43
    wceq
    @11
    @44
    cX
    @10
    @43
    unieq
    eqeq2d
    cbvrexv
    sylib
    alexsub
    ex
    impbid
end
