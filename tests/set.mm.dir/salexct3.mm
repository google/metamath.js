include "csalg.mm"
include "wcel.mm"
include "wss.mm"
include "cuni.mm"
include "wn.mm"
include "wtru.mm"
include "cvv.mm"
include "cc0.mm"
include "c2.mm"
include "cicc.mm"
include "co.mm"
include "ovex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "salexct.mm"
include "trud.mm"
include "c1.mm"
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
include "ciun.mm"
include "unieqi.mm"
include "snex.mm"
include "rgenw.mm"
include "dfiun3g.mm"
include "eqcomi.mm"
include "iunid.mm"
include "3eqtrri.mm"
include "salexct2.mm"
include "3pm3.2i.mm"

theorem salexct3
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cS: class S
  let cX: class X
  let vk: setvar k
  assume salexct3.a: |- A = ( 0 [,] 2 )
  assume salexct3.s: |- S = { x e. ~P A | ( x ~<_ _om \/ ( A \ x ) ~<_ _om ) }
  assume salexct3.x: |- X = ran ( y e. ( 0 [,] 1 ) |-> { y } )

  disjoint A x
  disjoint S x
  disjoint S y
  disjoint x y
  disjoint X x
  disjoint k x
  assert |- ( S e. SAlg /\ X C_ S /\ -. U. X e. S )

  proof
    cS
    csalg
    wcel
    #
    cX
    cS
    wss
    cX
    cuni
    #
    cS
    wcel
    wn
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
    cc0
    c2
    cicc
    co
    #
    cvv
    salexct3.a
    cc0
    c2
    cicc
    ovex
    eqeltri
    a1i
    salexct3.s
    salexct
    trud
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
    salexct3.x
    @5
    cS
    wcel
    #
    vy
    @3
    wral
    @7
    cS
    wss
    @8
    vy
    @3
    @4
    @3
    wcel
    #
    @5
    cA
    cpw
    #
    wcel
    #
    @5
    com
    cdom
    wbr
    #
    cA
    @5
    cdif
    #
    com
    cdom
    wbr
    #
    wo
    #
    wa
    @8
    @9
    @11
    @15
    @9
    @4
    cA
    wcel
    @11
    @9
    @4
    @2
    cA
    @9
    @3
    @2
    @4
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
    @3
    @2
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
    @9
    id
    sseldi
    salexct3.a
    syl6eleqr
    @4
    cA
    snelpwi
    syl
    @15
    @9
    @12
    @15
    @5
    cfn
    wcel
    @12
    @4
    snfi
    @5
    fict
    ax-mp
    @12
    @14
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
    @15
    vx
    @5
    @10
    cS
    @20
    @5
    wceq
    #
    @21
    @12
    @23
    @14
    @20
    @5
    com
    cdom
    breq1
    @24
    @22
    @13
    com
    cdom
    @20
    @5
    cA
    difeq2
    breq1d
    orbi12d
    salexct3.s
    elrab2
    sylibr
    rgen
    vy
    @3
    @5
    cS
    @6
    @6
    eqid
    rnmptss
    ax-mp
    eqsstri
    vx
    cA
    @1
    cS
    salexct3.a
    salexct3.s
    @3
    @1
    @1
    @7
    cuni
    #
    vy
    @3
    @5
    ciun
    #
    @3
    cX
    @7
    salexct3.x
    unieqi
    @26
    @25
    @5
    cvv
    wcel
    #
    vy
    @3
    wral
    @26
    @25
    wceq
    @27
    vy
    @3
    @4
    snex
    rgenw
    vy
    @3
    @5
    cvv
    dfiun3g
    ax-mp
    eqcomi
    vy
    @3
    iunid
    3eqtrri
    eqcomi
    salexct2
    3pm3.2i
end
