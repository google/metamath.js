include "wss.mm"
include "csalg.mm"
include "wcel.mm"
include "wn.mm"
include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "cv.mm"
include "csn.mm"
include "cmpt.mm"
include "crn.mm"
include "wral.mm"
include "cpw.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cdif.mm"
include "wo.mm"
include "wa.mm"
include "c2.mm"
include "cr.mm"
include "cle.mm"
include "0re.mm"
include "2re.mm"
include "pm3.2i.mm"
include "leidi.mm"
include "1le2.mm"
include "iccss.mm"
include "mp2an.mm"
include "id.mm"
include "sseldi.mm"
include "syl6eleqr.mm"
include "snelpwi.mm"
include "syl.mm"
include "cfn.mm"
include "snfi.mm"
include "fict.mm"
include "ax-mp.mm"
include "orc.mm"
include "a1i.mm"
include "jca.mm"
include "wceq.mm"
include "breq1.mm"
include "difeq2.mm"
include "breq1d.mm"
include "orbi12d.mm"
include "elrab2.mm"
include "sylibr.mm"
include "rgen.mm"
include "eqid.mm"
include "rnmptss.mm"
include "eqsstri.mm"
include "wtru.mm"
include "cvv.mm"
include "ovex.mm"
include "eqeltri.mm"
include "salexct.mm"
include "trud.mm"
include "mptex.mm"
include "rnex.mm"
include "cuni.mm"
include "ciun.mm"
include "unieqi.mm"
include "snex.mm"
include "rgenw.mm"
include "dfiun3g.mm"
include "eqcomi.mm"
include "iunid.mm"
include "3eqtrri.mm"
include "unisalgen.mm"
include "salexct2.mm"
include "nelss.mm"
include "3pm3.2i.mm"

theorem salgensscntex
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cS: class S
  let cG: class G
  let cX: class X
  let vk: setvar k
  assume salgensscntex.a: |- A = ( 0 [,] 2 )
  assume salgensscntex.s: |- S = { x e. ~P A | ( x ~<_ _om \/ ( A \ x ) ~<_ _om ) }
  assume salgensscntex.x: |- X = ran ( y e. ( 0 [,] 1 ) |-> { y } )
  assume salgensscntex.g: |- G = ( SalGen ` X )

  disjoint A x
  disjoint S x
  disjoint S y
  disjoint x y
  disjoint k x
  assert |- ( X C_ S /\ S e. SAlg /\ -. G C_ S )

  proof
    cX
    cS
    wss
    cS
    csalg
    wcel
    #
    cG
    cS
    wss
    wn
    #
    cX
    vy
    cc0
    c1
    cicc
    co
    #
    vy
    cv
    #
    csn
    #
    cmpt
    #
    crn
    #
    cS
    salgensscntex.x
    @4
    cS
    wcel
    #
    vy
    @2
    wral
    @6
    cS
    wss
    @7
    vy
    @2
    @3
    @2
    wcel
    #
    @4
    cA
    cpw
    #
    wcel
    #
    @4
    com
    cdom
    wbr
    #
    cA
    @4
    cdif
    #
    com
    cdom
    wbr
    #
    wo
    #
    wa
    @7
    @8
    @10
    @14
    @8
    @3
    cA
    wcel
    @10
    @8
    @3
    cc0
    c2
    cicc
    co
    #
    cA
    @8
    @2
    @15
    @3
    cc0
    cr
    wcel
    #
    c2
    cr
    wcel
    #
    wa
    cc0
    cc0
    cle
    wbr
    #
    c1
    c2
    cle
    wbr
    #
    wa
    @2
    @15
    wss
    @16
    @17
    0re
    2re
    pm3.2i
    @18
    @19
    cc0
    0re
    leidi
    1le2
    pm3.2i
    cc0
    c2
    cc0
    c1
    iccss
    mp2an
    @8
    id
    sseldi
    salgensscntex.a
    syl6eleqr
    @3
    cA
    snelpwi
    syl
    @14
    @8
    @11
    @14
    @4
    cfn
    wcel
    @11
    @3
    snfi
    @4
    fict
    ax-mp
    @11
    @13
    orc
    ax-mp
    a1i
    jca
    vx
    cv
    #
    com
    cdom
    wbr
    #
    cA
    @20
    cdif
    #
    com
    cdom
    wbr
    #
    wo
    @14
    vx
    @4
    @9
    cS
    @20
    @4
    wceq
    #
    @21
    @11
    @23
    @13
    @20
    @4
    com
    cdom
    breq1
    @24
    @22
    @12
    com
    cdom
    @20
    @4
    cA
    difeq2
    breq1d
    orbi12d
    salgensscntex.s
    elrab2
    sylibr
    rgen
    vy
    @2
    @4
    cS
    @5
    @5
    eqid
    rnmptss
    ax-mp
    eqsstri
    @0
    wtru
    vx
    cA
    cS
    cvv
    cA
    cvv
    wcel
    wtru
    cA
    @15
    cvv
    salgensscntex.a
    cc0
    c2
    cicc
    ovex
    eqeltri
    a1i
    salgensscntex.s
    salexct
    trud
    @2
    cG
    wcel
    #
    @2
    cS
    wcel
    wn
    @1
    @25
    wtru
    cG
    @2
    cvv
    cX
    cX
    cvv
    wcel
    wtru
    cX
    @6
    cvv
    salgensscntex.x
    @5
    vy
    @2
    @4
    cc0
    c1
    cicc
    ovex
    mptex
    rnex
    eqeltri
    a1i
    salgensscntex.g
    cX
    cuni
    @6
    cuni
    #
    vy
    @2
    @4
    ciun
    #
    @2
    cX
    @6
    salgensscntex.x
    unieqi
    @27
    @26
    @4
    cvv
    wcel
    #
    vy
    @2
    wral
    @27
    @26
    wceq
    @28
    vy
    @2
    @3
    snex
    rgenw
    vy
    @2
    @4
    cvv
    dfiun3g
    ax-mp
    eqcomi
    vy
    @2
    iunid
    3eqtrri
    unisalgen
    trud
    vx
    cA
    @2
    cS
    salgensscntex.a
    salgensscntex.s
    @2
    eqid
    salexct2
    @2
    cG
    cS
    nelss
    mp2an
    3pm3.2i
end
