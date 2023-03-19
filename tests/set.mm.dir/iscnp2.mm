include "ccnp.mm"
include "co.mm"
include "cfv.mm"
include "wcel.mm"
include "ctop.mm"
include "w3a.mm"
include "wf.mm"
include "cv.mm"
include "cima.mm"
include "wss.mm"
include "wa.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "cop.mm"
include "cxp.mm"
include "cdm.mm"
include "c0.mm"
include "wceq.mm"
include "n0i.mm"
include "wn.mm"
include "df-ov.mm"
include "ndmfv.mm"
include "syl5eq.mm"
include "fveq1d.mm"
include "0fv.mm"
include "syl6eq.mm"
include "nsyl2.mm"
include "cuni.mm"
include "cmap.mm"
include "crab.mm"
include "cmpt.mm"
include "df-cnp.mm"
include "cpw.mm"
include "cvv.mm"
include "ssrab2.mm"
include "ovex.mm"
include "elpw2.mm"
include "mpbir.mm"
include "rgenw.mm"
include "eqid.mm"
include "fmpt.mm"
include "mpbi.mm"
include "vuniex.mm"
include "pwex.mm"
include "fex2.mm"
include "mp3an.mm"
include "dmmpt2.mm"
include "syl6eleq.mm"
include "opelxp.mm"
include "sylib.mm"
include "simpld.mm"
include "simprd.mm"
include "elfvdm.mm"
include "ctopon.mm"
include "toptopon.mm"
include "cnpfval.mm"
include "syl2anb.mm"
include "syl.mm"
include "dmeqd.mm"
include "rabex.mm"
include "dmmptg.mm"
include "ax-mp.mm"
include "eleqtrd.mm"
include "3jca.mm"
include "wb.mm"
include "biid.mm"
include "iscnp.mm"
include "syl3anb.mm"
include "biadan2.mm"

theorem iscnp2
  let vx: setvar x
  let vy: setvar y
  let cP: class P
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vg: setvar g
  let vj: setvar j
  let vk: setvar k
  let vv: setvar v
  let vw: setvar w
  assume iscn.1: |- X = U. J
  assume iscn.2: |- Y = U. K

  disjoint x y
  disjoint J x
  disjoint J y
  disjoint K x
  disjoint K y
  disjoint X x
  disjoint X y
  disjoint F x
  disjoint F y
  disjoint P x
  disjoint P y
  disjoint Y x
  disjoint Y y
  disjoint f g
  disjoint f j
  disjoint f k
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint J f
  disjoint g j
  disjoint g k
  disjoint g v
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint J g
  disjoint j k
  disjoint j v
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint J j
  disjoint k v
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint J k
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint J v
  disjoint w x
  disjoint w y
  disjoint J w
  disjoint K f
  disjoint K j
  disjoint K k
  disjoint K v
  disjoint K w
  disjoint X f
  disjoint X j
  disjoint X k
  disjoint X v
  disjoint X w
  disjoint F f
  disjoint P f
  disjoint P v
  disjoint Y f
  disjoint Y j
  disjoint Y k
  disjoint Y v
  disjoint Y w
  assert |- ( F e. ( ( J CnP K ) ` P ) <-> ( ( J e. Top /\ K e. Top /\ P e. X ) /\ ( F : X --> Y /\ A. y e. K ( ( F ` P ) e. y -> E. x e. J ( P e. x /\ ( F " x ) C_ y ) ) ) ) )

  proof
    cF
    cP
    cJ
    cK
    ccnp
    co
    #
    cfv
    #
    wcel
    #
    cJ
    ctop
    wcel
    #
    cK
    ctop
    wcel
    #
    cP
    cX
    wcel
    #
    w3a
    cX
    cY
    cF
    wf
    cP
    cF
    cfv
    vy
    cv
    #
    wcel
    cP
    vx
    cv
    #
    wcel
    cF
    @7
    cima
    @6
    wss
    wa
    vx
    cJ
    wrex
    wi
    vy
    cK
    wral
    wa
    #
    @2
    @3
    @4
    @5
    @2
    @3
    @4
    @2
    cJ
    cK
    cop
    #
    ctop
    ctop
    cxp
    #
    wcel
    @3
    @4
    wa
    #
    @2
    @9
    ccnp
    cdm
    #
    @10
    @2
    @1
    c0
    wceq
    @9
    @12
    wcel
    #
    @1
    cF
    n0i
    @13
    wn
    #
    @1
    cP
    c0
    cfv
    c0
    @14
    cP
    @0
    c0
    @14
    @0
    @9
    ccnp
    cfv
    c0
    cJ
    cK
    ccnp
    df-ov
    @9
    ccnp
    ndmfv
    syl5eq
    fveq1d
    cP
    0fv
    syl6eq
    nsyl2
    vj
    vk
    ctop
    ctop
    vx
    vj
    cv
    #
    cuni
    #
    @7
    vf
    cv
    #
    cfv
    #
    @6
    wcel
    @7
    vg
    cv
    #
    wcel
    @17
    @19
    cima
    @6
    wss
    wa
    vg
    @15
    wrex
    wi
    vy
    vk
    cv
    #
    wral
    #
    vf
    @20
    cuni
    #
    @16
    cmap
    co
    #
    crab
    #
    cmpt
    #
    ccnp
    vx
    vy
    vf
    vg
    vj
    vk
    df-cnp
    @16
    @23
    cpw
    #
    @25
    wf
    #
    @16
    cvv
    wcel
    @26
    cvv
    wcel
    @25
    cvv
    wcel
    @24
    @26
    wcel
    #
    vx
    @16
    wral
    @27
    @28
    vx
    @16
    @28
    @24
    @23
    wss
    @21
    vf
    @23
    ssrab2
    @24
    @23
    @22
    @16
    cmap
    ovex
    #
    elpw2
    mpbir
    rgenw
    vx
    @16
    @26
    @24
    @25
    @25
    eqid
    fmpt
    mpbi
    vj
    vuniex
    @23
    @29
    pwex
    @16
    @26
    @25
    cvv
    cvv
    fex2
    mp3an
    dmmpt2
    syl6eleq
    cJ
    cK
    ctop
    ctop
    opelxp
    sylib
    #
    simpld
    @2
    @3
    @4
    @30
    simprd
    @2
    cP
    @0
    cdm
    #
    cX
    cF
    cP
    @0
    elfvdm
    @2
    @31
    vx
    cX
    @18
    vw
    cv
    #
    wcel
    @7
    vv
    cv
    #
    wcel
    @17
    @33
    cima
    @32
    wss
    wa
    vv
    cJ
    wrex
    wi
    vw
    cK
    wral
    #
    vf
    cY
    cX
    cmap
    co
    #
    crab
    #
    cmpt
    #
    cdm
    #
    cX
    @2
    @0
    @37
    @2
    @11
    @0
    @37
    wceq
    #
    @30
    @3
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cK
    cY
    ctopon
    cfv
    wcel
    #
    @39
    @4
    cJ
    cX
    iscn.1
    toptopon
    #
    cK
    cY
    iscn.2
    toptopon
    #
    vx
    vw
    vv
    vf
    cJ
    cK
    cX
    cY
    cnpfval
    syl2anb
    syl
    dmeqd
    @36
    cvv
    wcel
    #
    vx
    cX
    wral
    @38
    cX
    wceq
    @44
    vx
    cX
    @34
    vf
    @35
    cY
    cX
    cmap
    ovex
    rabex
    rgenw
    vx
    cX
    @36
    cvv
    dmmptg
    ax-mp
    syl6eq
    eleqtrd
    3jca
    @3
    @40
    @4
    @41
    @5
    @5
    @2
    @8
    wb
    @42
    @43
    @5
    biid
    vx
    vy
    cP
    cF
    cJ
    cK
    cX
    cY
    iscnp
    syl3anb
    biadan2
end
