include "wcel.mm"
include "cv.mm"
include "cuni.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "c0.mm"
include "csn.mm"
include "cif.mm"
include "cfne.mm"
include "wbr.mm"
include "unisng.mm"
include "eqcomd.mm"
include "adantr.mm"
include "iftrue.mm"
include "unieqd.mm"
include "eqeq2d.mm"
include "syl5ibrcom.mm"
include "wne.mm"
include "wex.mm"
include "n0.mm"
include "w3a.mm"
include "unieq.mm"
include "rspccva.mm"
include "3adant1.mm"
include "fnejoin1.mm"
include "eqid.mm"
include "fnebas.mm"
include "syl.mm"
include "eqtrd.mm"
include "3expia.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "pm2.61dne.mm"
include "sylan9eq.mm"
include "ex.mm"
include "wi.mm"
include "fnetr.mm"
include "3expa.mm"
include "ralrimdva.mm"
include "jcad.mm"
include "ctg.mm"
include "cfv.mm"
include "wss.mm"
include "simprl.mm"
include "eqtr3d.mm"
include "sseq1.mm"
include "cvv.mm"
include "elex.mm"
include "ad2antrr.mm"
include "eqeltrrd.mm"
include "uniexb.mm"
include "sylibr.mm"
include "ssid.mm"
include "eltg3i.mm"
include "sylancl.mm"
include "eqeltrd.mm"
include "snssd.mm"
include "wn.mm"
include "simplrr.mm"
include "fnetg.mm"
include "ralimi.mm"
include "unissb.mm"
include "ifbothda.mm"
include "isfne4.mm"
include "sylanbrc.mm"
include "impbid.mm"

theorem fnejoin2
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  let cT: class T
  let cV: class V
  let cX: class X
  let vt: setvar t
  let cA: class A
  let vj: setvar j
  let vk: setvar k

  disjoint x y
  disjoint S x
  disjoint S y
  disjoint V x
  disjoint X x
  disjoint X y
  disjoint T x
  disjoint t y
  disjoint A t
  disjoint A y
  disjoint j k
  disjoint j t
  disjoint j x
  disjoint j y
  disjoint S j
  disjoint k t
  disjoint k x
  disjoint k y
  disjoint S k
  disjoint t x
  disjoint S t
  disjoint V j
  disjoint V k
  disjoint V t
  disjoint X j
  disjoint X k
  disjoint X t
  disjoint T t
  assert |- ( ( X e. V /\ A. y e. S X = U. y ) -> ( if ( S = (/) , { X } , U. S ) Fne T <-> ( X = U. T /\ A. x e. S x Fne T ) ) )

  proof
    cX
    cV
    wcel
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
    cS
    wral
    #
    wa
    #
    cS
    c0
    wceq
    #
    cX
    csn
    #
    cS
    cuni
    #
    cif
    #
    cT
    cfne
    wbr
    #
    cX
    cT
    cuni
    #
    wceq
    #
    vx
    cv
    #
    cT
    cfne
    wbr
    #
    vx
    cS
    wral
    #
    wa
    #
    @5
    @10
    @12
    @15
    @5
    @10
    @12
    @5
    @10
    cX
    @9
    cuni
    #
    @11
    @5
    cX
    @17
    wceq
    #
    cS
    c0
    @5
    @18
    @6
    cX
    @7
    cuni
    #
    wceq
    #
    @0
    @20
    @4
    @0
    @19
    cX
    cX
    cV
    unisng
    eqcomd
    adantr
    @6
    @17
    @19
    cX
    @6
    @9
    @7
    @6
    @7
    @8
    iftrue
    unieqd
    eqeq2d
    syl5ibrcom
    cS
    c0
    wne
    @13
    cS
    wcel
    #
    vx
    wex
    @5
    @18
    vx
    cS
    n0
    @5
    @21
    @18
    vx
    @0
    @4
    @21
    @18
    @0
    @4
    @21
    w3a
    #
    cX
    @13
    cuni
    #
    @17
    @4
    @21
    cX
    @23
    wceq
    #
    @0
    @3
    @24
    vy
    @13
    cS
    @1
    @13
    wceq
    @2
    @23
    cX
    @1
    @13
    unieq
    eqeq2d
    rspccva
    3adant1
    @22
    @13
    @9
    cfne
    wbr
    #
    @23
    @17
    wceq
    vy
    @13
    cS
    cV
    cX
    fnejoin1
    #
    @13
    @9
    @23
    @17
    @23
    eqid
    @17
    eqid
    #
    fnebas
    syl
    eqtrd
    3expia
    exlimdv
    syl5bi
    pm2.61dne
    #
    @9
    cT
    @17
    @11
    @27
    @11
    eqid
    #
    fnebas
    sylan9eq
    ex
    @5
    @10
    @14
    vx
    cS
    @0
    @4
    @21
    @10
    @14
    wi
    #
    @22
    @25
    @30
    @26
    @25
    @10
    @14
    @13
    @9
    cT
    fnetr
    ex
    syl
    3expa
    ralrimdva
    jcad
    @5
    @16
    @10
    @5
    @16
    wa
    #
    @17
    @11
    wceq
    @9
    cT
    ctg
    cfv
    #
    wss
    #
    @10
    @31
    cX
    @17
    @11
    @5
    @18
    @16
    @28
    adantr
    @5
    @12
    @15
    simprl
    #
    eqtr3d
    @6
    @7
    @32
    wss
    #
    @8
    @32
    wss
    #
    @33
    @31
    @7
    @8
    @7
    @9
    @32
    sseq1
    @8
    @9
    @32
    sseq1
    @31
    @35
    @6
    @31
    cX
    @32
    @31
    cX
    @11
    @32
    @34
    @31
    cT
    cvv
    wcel
    #
    cT
    cT
    wss
    @11
    @32
    wcel
    @31
    @11
    cvv
    wcel
    @37
    @31
    cX
    @11
    cvv
    @34
    @0
    cX
    cvv
    wcel
    @4
    @16
    cX
    cV
    elex
    ad2antrr
    eqeltrrd
    cT
    uniexb
    sylibr
    cT
    ssid
    cT
    cT
    cvv
    eltg3i
    sylancl
    eqeltrd
    snssd
    adantr
    @31
    @6
    wn
    #
    wa
    #
    @13
    @32
    wss
    #
    vx
    cS
    wral
    #
    @36
    @39
    @15
    @41
    @5
    @12
    @15
    @38
    simplrr
    @14
    @40
    vx
    cS
    @13
    cT
    fnetg
    ralimi
    syl
    vx
    cS
    @32
    unissb
    sylibr
    ifbothda
    @9
    cT
    @17
    @11
    @27
    @29
    isfne4
    sylanbrc
    ex
    impbid
end
