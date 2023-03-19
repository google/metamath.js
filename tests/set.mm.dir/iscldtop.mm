include "ccld.mm"
include "ctopon.mm"
include "cfv.mm"
include "cima.mm"
include "wcel.mm"
include "cmre.mm"
include "c0.mm"
include "cv.mm"
include "cun.mm"
include "wral.mm"
include "w3a.mm"
include "wceq.mm"
include "wrex.mm"
include "wfun.mm"
include "ctop.mm"
include "wfn.mm"
include "fncld.mm"
include "fnfun.mm"
include "ax-mp.mm"
include "fvelima.mm"
include "mpan.mm"
include "cldmreon.mm"
include "topontop.mm"
include "0cld.mm"
include "syl.mm"
include "wa.mm"
include "uncld.mm"
include "adantl.mm"
include "ralrimivva.mm"
include "3jca.mm"
include "eleq1.mm"
include "eleq2.mm"
include "raleqbi1dv.mm"
include "3anbi123d.mm"
include "syl5ibcom.mm"
include "rexlimiv.mm"
include "cdif.mm"
include "cpw.mm"
include "crab.mm"
include "simp1.mm"
include "simp2.mm"
include "wi.mm"
include "uneq1.mm"
include "eleq1d.mm"
include "uneq2.mm"
include "rspc2v.mm"
include "com12.mm"
include "3ad2ant3.mm"
include "3impib.mm"
include "eqid.mm"
include "mretopd.mm"
include "simprd.mm"
include "simpld.mm"
include "cdm.mm"
include "wss.mm"
include "ssriv.mm"
include "fndm.mm"
include "sseqtr4i.mm"
include "funfvima2.mm"
include "mp2an.mm"
include "eqeltrd.mm"
include "impbii.mm"

theorem iscldtop
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cK: class K
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let cV: class V

  disjoint B x
  disjoint B y
  disjoint x y
  disjoint K x
  disjoint K y
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint a b
  disjoint a c
  disjoint a x
  disjoint a y
  disjoint b c
  disjoint b x
  disjoint b y
  disjoint c x
  disjoint c y
  disjoint V a
  disjoint V b
  disjoint V c
  disjoint V x
  disjoint V y
  disjoint K a
  disjoint K b
  disjoint K c
  assert |- ( K e. ( Clsd " ( TopOn ` B ) ) <-> ( K e. ( Moore ` B ) /\ (/) e. K /\ A. x e. K A. y e. K ( x u. y ) e. K ) )

  proof
    cK
    ccld
    cB
    ctopon
    cfv
    #
    cima
    #
    wcel
    #
    cK
    cB
    cmre
    cfv
    #
    wcel
    #
    c0
    cK
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cun
    #
    cK
    wcel
    #
    vy
    cK
    wral
    #
    vx
    cK
    wral
    #
    w3a
    #
    @2
    va
    cv
    #
    ccld
    cfv
    #
    cK
    wceq
    #
    va
    @0
    wrex
    #
    @12
    ccld
    wfun
    #
    @2
    @16
    ccld
    ctop
    wfn
    #
    @17
    fncld
    ctop
    ccld
    fnfun
    ax-mp
    #
    va
    cK
    @0
    ccld
    fvelima
    mpan
    @15
    @12
    va
    @0
    @13
    @0
    wcel
    #
    @14
    @3
    wcel
    #
    c0
    @14
    wcel
    #
    @8
    @14
    wcel
    #
    vy
    @14
    wral
    #
    vx
    @14
    wral
    #
    w3a
    @15
    @12
    @20
    @21
    @22
    @25
    cB
    @13
    cldmreon
    @20
    @13
    ctop
    wcel
    @22
    cB
    @13
    topontop
    #
    @13
    0cld
    syl
    @20
    @23
    vx
    vy
    @14
    @14
    @6
    @14
    wcel
    @7
    @14
    wcel
    wa
    @23
    @20
    @6
    @7
    @13
    uncld
    adantl
    ralrimivva
    3jca
    @15
    @21
    @4
    @22
    @5
    @25
    @11
    @14
    cK
    @3
    eleq1
    @14
    cK
    c0
    eleq2
    @24
    @10
    vx
    @14
    cK
    @23
    @9
    vy
    @14
    cK
    @14
    cK
    @8
    eleq2
    raleqbi1dv
    raleqbi1dv
    3anbi123d
    syl5ibcom
    rexlimiv
    syl
    @12
    cK
    cB
    @13
    cdif
    cK
    wcel
    va
    cB
    cpw
    crab
    #
    ccld
    cfv
    #
    @1
    @12
    @27
    @0
    wcel
    #
    cK
    @28
    wceq
    #
    @12
    vb
    vc
    va
    cB
    @27
    cK
    @4
    @5
    @11
    simp1
    @4
    @5
    @11
    simp2
    @12
    vb
    cv
    #
    cK
    wcel
    #
    vc
    cv
    #
    cK
    wcel
    #
    @31
    @33
    cun
    #
    cK
    wcel
    #
    @11
    @4
    @32
    @34
    wa
    #
    @36
    wi
    @5
    @37
    @11
    @36
    @9
    @36
    @31
    @7
    cun
    #
    cK
    wcel
    vx
    vy
    @31
    @33
    cK
    cK
    @6
    @31
    wceq
    @8
    @38
    cK
    @6
    @31
    @7
    uneq1
    eleq1d
    @7
    @33
    wceq
    @38
    @35
    cK
    @7
    @33
    @31
    uneq2
    eleq1d
    rspc2v
    com12
    3ad2ant3
    3impib
    @27
    eqid
    mretopd
    #
    simprd
    @12
    @29
    @28
    @1
    wcel
    #
    @12
    @29
    @30
    @39
    simpld
    @17
    @0
    ccld
    cdm
    #
    wss
    @29
    @40
    wi
    @19
    @0
    ctop
    @41
    va
    @0
    ctop
    @26
    ssriv
    @18
    @41
    ctop
    wceq
    fncld
    ctop
    ccld
    fndm
    ax-mp
    sseqtr4i
    @0
    @27
    ccld
    funfvima2
    mp2an
    syl
    eqeltrd
    impbii
end
