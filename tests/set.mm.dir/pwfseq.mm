include "cvv.mm"
include "wcel.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cpw.mm"
include "cv.mm"
include "cmap.mm"
include "co.mm"
include "ciun.mm"
include "wn.mm"
include "reldom.mm"
include "brrelex2i.mm"
include "cen.mm"
include "wss.mm"
include "wa.mm"
include "wex.mm"
include "domeng.mm"
include "wf1o.mm"
include "wi.mm"
include "bren.mm"
include "cxp.mm"
include "cfv.mm"
include "char.mm"
include "wral.mm"
include "con0.mm"
include "harcl.mm"
include "infxpenc2.mm"
include "ax-mp.mm"
include "wf1.mm"
include "wwe.mm"
include "w3a.mm"
include "coi.mm"
include "cdm.mm"
include "ccom.mm"
include "cop.mm"
include "cmpt2.mm"
include "ccnv.mm"
include "csuc.mm"
include "cres.mm"
include "cmpt.mm"
include "c0.mm"
include "csn.mm"
include "cseqom.mm"
include "simpr.mm"
include "wceq.mm"
include "wb.mm"
include "oveq2.mm"
include "cbviunv.mm"
include "f1eq3.mm"
include "sylib.mm"
include "simpllr.mm"
include "simplll.mm"
include "biid.mm"
include "simplr.mm"
include "sseq2.mm"
include "fveq2.mm"
include "f1oeq1.mm"
include "syl.mm"
include "xpeq12.mm"
include "anidms.mm"
include "f1oeq2.mm"
include "f1oeq3.mm"
include "3bitrd.mm"
include "imbi12d.mm"
include "cbvralv.mm"
include "eqid.mm"
include "mpteq1.mm"
include "pwfseqlem5.mm"
include "imnani.mm"
include "nexdv.mm"
include "brdomi.mm"
include "nsyl.mm"
include "ex.mm"
include "exlimdv.mm"
include "mpi.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "imp.mm"
include "syl6bi.mm"
include "mpcom.mm"

theorem pwfseq
  let cA: class A
  let vn: setvar n
  let vb: setvar b
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vk: setvar k
  let vm: setvar m
  let vp: setvar p
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint A n
  disjoint b f
  disjoint b g
  disjoint b h
  disjoint b k
  disjoint b m
  disjoint b n
  disjoint b p
  disjoint b r
  disjoint b s
  disjoint b t
  disjoint b u
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint A b
  disjoint f g
  disjoint f h
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint f p
  disjoint f r
  disjoint f s
  disjoint f t
  disjoint f u
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint g h
  disjoint g k
  disjoint g m
  disjoint g n
  disjoint g p
  disjoint g r
  disjoint g s
  disjoint g t
  disjoint g u
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint h k
  disjoint h m
  disjoint h n
  disjoint h p
  disjoint h r
  disjoint h s
  disjoint h t
  disjoint h u
  disjoint h w
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint A h
  disjoint k m
  disjoint k n
  disjoint k p
  disjoint k r
  disjoint k s
  disjoint k t
  disjoint k u
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint m n
  disjoint m p
  disjoint m r
  disjoint m s
  disjoint m t
  disjoint m u
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n p
  disjoint n r
  disjoint n s
  disjoint n t
  disjoint n u
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint p r
  disjoint p s
  disjoint p t
  disjoint p u
  disjoint p w
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint A p
  disjoint r s
  disjoint r t
  disjoint r u
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint A r
  disjoint s t
  disjoint s u
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint t u
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint A t
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  assert |- ( _om ~<_ A -> -. ~P A ~<_ U_ n e. _om ( A ^m n ) )

  proof
    cA
    cvv
    wcel
    #
    com
    cA
    cdom
    wbr
    #
    cA
    cpw
    #
    vn
    com
    cA
    vn
    cv
    #
    cmap
    co
    #
    ciun
    #
    cdom
    wbr
    #
    wn
    #
    com
    cA
    cdom
    reldom
    brrelex2i
    @0
    @1
    com
    vt
    cv
    #
    cen
    wbr
    #
    @8
    cA
    wss
    #
    wa
    #
    vt
    wex
    @7
    vt
    com
    cA
    cvv
    domeng
    @11
    @7
    vt
    @9
    @10
    @7
    @9
    com
    @8
    vh
    cv
    #
    wf1o
    #
    vh
    wex
    @10
    @7
    wi
    #
    com
    @8
    vh
    bren
    @13
    @14
    vh
    @13
    @10
    @7
    @13
    @10
    wa
    #
    com
    vb
    cv
    #
    wss
    #
    @16
    @16
    cxp
    #
    @16
    @16
    vm
    cv
    #
    cfv
    #
    wf1o
    #
    wi
    #
    vb
    @2
    char
    cfv
    #
    wral
    #
    vm
    wex
    #
    @7
    @23
    con0
    wcel
    @25
    @2
    harcl
    @23
    vm
    vb
    infxpenc2
    ax-mp
    @15
    @24
    @7
    vm
    @15
    @24
    @7
    @15
    @24
    wa
    #
    @2
    @5
    vg
    cv
    #
    wf1
    #
    vg
    wex
    @6
    @26
    @28
    vg
    @26
    @28
    @26
    @28
    wa
    #
    vu
    cv
    #
    cA
    wss
    vr
    cv
    #
    @30
    @30
    cxp
    wss
    @30
    @31
    wwe
    w3a
    com
    @30
    cdom
    wbr
    wa
    #
    vx
    vy
    vz
    vs
    vu
    cA
    @30
    @31
    coi
    #
    @33
    cdm
    #
    @19
    cfv
    ccom
    vs
    vz
    @34
    @34
    vs
    cv
    @33
    cfv
    vz
    cv
    @33
    cfv
    cop
    cmpt2
    #
    ccnv
    ccom
    #
    vy
    vn
    com
    @30
    @3
    cmap
    co
    #
    ciun
    #
    vy
    cv
    #
    cdm
    #
    @39
    @40
    vp
    vf
    cvv
    cvv
    vx
    @30
    vp
    cv
    #
    csuc
    cmap
    co
    vx
    cv
    #
    @41
    cres
    vf
    cv
    cfv
    @41
    @42
    cfv
    @36
    co
    cmpt
    cmpt2
    c0
    c0
    @33
    cfv
    cop
    csn
    cseqom
    #
    cfv
    cfv
    cop
    #
    cmpt
    #
    @43
    @35
    vf
    vp
    vk
    @27
    @12
    vx
    vy
    com
    @30
    @42
    @33
    cfv
    @39
    cop
    cmpt2
    #
    @36
    @46
    ccom
    @45
    ccom
    #
    @19
    @33
    @8
    vr
    vw
    @29
    @28
    @2
    vk
    com
    cA
    vk
    cv
    #
    cmap
    co
    #
    ciun
    #
    @27
    wf1
    #
    @26
    @28
    simpr
    @5
    @50
    wceq
    @28
    @51
    wb
    vn
    vk
    com
    @4
    @49
    @3
    @48
    cA
    cmap
    oveq2
    cbviunv
    @5
    @50
    @2
    @27
    f1eq3
    ax-mp
    sylib
    @13
    @10
    @24
    @28
    simpllr
    @13
    @10
    @24
    @28
    simplll
    @32
    biid
    @29
    @24
    com
    vw
    cv
    #
    wss
    #
    @52
    @52
    cxp
    #
    @52
    @52
    @19
    cfv
    #
    wf1o
    #
    wi
    #
    vw
    @23
    wral
    @15
    @24
    @28
    simplr
    @22
    @57
    vb
    vw
    @23
    @16
    @52
    wceq
    #
    @17
    @53
    @21
    @56
    @16
    @52
    com
    sseq2
    @58
    @21
    @18
    @16
    @55
    wf1o
    #
    @54
    @16
    @55
    wf1o
    #
    @56
    @58
    @20
    @55
    wceq
    @21
    @59
    wb
    @16
    @52
    @19
    fveq2
    @18
    @16
    @20
    @55
    f1oeq1
    syl
    @58
    @18
    @54
    wceq
    #
    @59
    @60
    wb
    @58
    @61
    @16
    @52
    @16
    @52
    xpeq12
    anidms
    @18
    @54
    @16
    @55
    f1oeq2
    syl
    @16
    @52
    @54
    @55
    f1oeq3
    3bitrd
    imbi12d
    cbvralv
    sylib
    @33
    eqid
    @35
    eqid
    @36
    eqid
    @43
    eqid
    @38
    vk
    com
    @30
    @48
    cmap
    co
    #
    ciun
    #
    wceq
    @45
    vy
    @63
    @44
    cmpt
    wceq
    vn
    vk
    com
    @37
    @62
    @3
    @48
    @30
    cmap
    oveq2
    cbviunv
    vy
    @38
    @63
    @44
    mpteq1
    ax-mp
    @46
    eqid
    @47
    eqid
    pwfseqlem5
    imnani
    nexdv
    @2
    @5
    vg
    brdomi
    nsyl
    ex
    exlimdv
    mpi
    ex
    exlimiv
    sylbi
    imp
    exlimiv
    syl6bi
    mpcom
end
