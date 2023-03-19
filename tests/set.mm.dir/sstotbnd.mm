include "cme.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "ctotbnd.mm"
include "cv.mm"
include "cbl.mm"
include "co.mm"
include "ciun.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "crp.mm"
include "wral.mm"
include "cuni.mm"
include "wceq.mm"
include "sstotbnd2.mm"
include "cmpt.mm"
include "crn.mm"
include "cab.mm"
include "elfpw.mm"
include "simprbi.mm"
include "mptfi.mm"
include "rnfi.mm"
include "3syl.mm"
include "ad2antrl.mm"
include "simprr.mm"
include "eqid.mm"
include "rnmpt.mm"
include "wi.mm"
include "simplbi.mm"
include "ssrexv.mm"
include "syl.mm"
include "ss2abdv.mm"
include "syl5eqss.mm"
include "unieq.mm"
include "ovex.mm"
include "dfiun3.mm"
include "syl6eqr.mm"
include "sseq2d.mm"
include "ssabral.mm"
include "sseq1.mm"
include "syl5bbr.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "rexlimdvaa.mm"
include "wf.mm"
include "wex.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "ac6sfi.mm"
include "adantrl.mm"
include "adantl.mm"
include "frn.mm"
include "wfo.mm"
include "simplrl.mm"
include "wfn.mm"
include "ffn.mm"
include "dffn4.mm"
include "sylib.mm"
include "fofi.mm"
include "syl2anc.mm"
include "sylanbrc.mm"
include "simprrl.mm"
include "adantr.mm"
include "uniiun.mm"
include "iuneq2.mm"
include "syl5eq.mm"
include "ad2antll.mm"
include "sseqtrd.mm"
include "eleq2d.mm"
include "rexrn.mm"
include "eliun.mm"
include "3bitr4g.mm"
include "eqrdv.mm"
include "sseqtr4d.mm"
include "iuneq1.mm"
include "exlimddv.mm"
include "impbid.mm"
include "ralbidv.mm"
include "bitrd.mm"

theorem sstotbnd
  let vx: setvar x
  let vv: setvar v
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y
  let vb: setvar b
  let vd: setvar d
  let vc: setvar c
  let vf: setvar f
  let vu: setvar u
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume sstotbnd.2: |- N = ( M |` ( Y X. Y ) )

  disjoint b d
  disjoint b v
  disjoint b x
  disjoint M b
  disjoint d v
  disjoint d x
  disjoint M d
  disjoint v x
  disjoint M v
  disjoint M x
  disjoint X b
  disjoint X d
  disjoint X v
  disjoint X x
  disjoint N d
  disjoint N v
  disjoint N x
  disjoint Y b
  disjoint Y d
  disjoint Y v
  disjoint Y x
  disjoint b c
  disjoint b f
  disjoint b u
  disjoint b w
  disjoint b y
  disjoint b z
  disjoint c d
  disjoint c f
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint M c
  disjoint d f
  disjoint d u
  disjoint d w
  disjoint d y
  disjoint d z
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint M f
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint M u
  disjoint v w
  disjoint v y
  disjoint v z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint M w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint M y
  disjoint M z
  disjoint X c
  disjoint X f
  disjoint X u
  disjoint X w
  disjoint X y
  disjoint X z
  disjoint N c
  disjoint N f
  disjoint N u
  disjoint N w
  disjoint N y
  disjoint N z
  disjoint Y c
  disjoint Y f
  disjoint Y u
  disjoint Y w
  disjoint Y y
  disjoint Y z
  assert |- ( ( M e. ( Met ` X ) /\ Y C_ X ) -> ( N e. ( TotBnd ` Y ) <-> A. d e. RR+ E. v e. Fin ( Y C_ U. v /\ A. b e. v E. x e. X b = ( x ( ball ` M ) d ) ) ) )

  proof
    cM
    cX
    cme
    cfv
    wcel
    cY
    cX
    wss
    wa
    #
    cN
    cY
    ctotbnd
    cfv
    wcel
    cY
    vx
    vu
    cv
    #
    vx
    cv
    #
    vd
    cv
    #
    cM
    cbl
    cfv
    #
    co
    #
    ciun
    #
    wss
    #
    vu
    cX
    cpw
    cfn
    cin
    #
    wrex
    #
    vd
    crp
    wral
    cY
    vv
    cv
    #
    cuni
    #
    wss
    #
    vb
    cv
    #
    @5
    wceq
    #
    vx
    cX
    wrex
    #
    vb
    @10
    wral
    #
    wa
    #
    vv
    cfn
    wrex
    #
    vd
    crp
    wral
    vx
    vu
    cM
    cN
    cX
    cY
    vd
    sstotbnd.2
    sstotbnd2
    @0
    @9
    @18
    vd
    crp
    @0
    @9
    @18
    @0
    @7
    @18
    vu
    @8
    @0
    @1
    @8
    wcel
    #
    @7
    wa
    wa
    #
    vx
    @1
    @5
    cmpt
    #
    crn
    #
    cfn
    wcel
    #
    @7
    @22
    @15
    vb
    cab
    #
    wss
    #
    @18
    @19
    @23
    @0
    @7
    @19
    @1
    cfn
    wcel
    #
    @21
    cfn
    wcel
    @23
    @19
    @1
    cX
    wss
    #
    @26
    @1
    cX
    elfpw
    #
    simprbi
    vx
    @1
    @5
    mptfi
    @21
    rnfi
    3syl
    ad2antrl
    @0
    @19
    @7
    simprr
    @20
    @22
    @14
    vx
    @1
    wrex
    #
    vb
    cab
    @24
    vx
    vb
    @1
    @5
    @21
    @21
    eqid
    rnmpt
    @20
    @29
    @15
    vb
    @19
    @29
    @15
    wi
    #
    @0
    @7
    @19
    @27
    @30
    @19
    @27
    @26
    @28
    simplbi
    @14
    vx
    @1
    cX
    ssrexv
    syl
    ad2antrl
    ss2abdv
    syl5eqss
    @17
    @7
    @25
    wa
    vv
    @22
    cfn
    @10
    @22
    wceq
    #
    @12
    @7
    @16
    @25
    @31
    @11
    @6
    cY
    @31
    @11
    @22
    cuni
    @6
    @10
    @22
    unieq
    vx
    @1
    @5
    @2
    @3
    @4
    ovex
    dfiun3
    syl6eqr
    sseq2d
    @16
    @10
    @24
    wss
    @31
    @25
    @15
    vb
    @10
    ssabral
    @10
    @22
    @24
    sseq1
    syl5bbr
    anbi12d
    rspcev
    syl12anc
    rexlimdvaa
    @0
    @17
    @9
    vv
    cfn
    @0
    @10
    cfn
    wcel
    #
    @17
    wa
    #
    wa
    #
    @10
    cX
    vf
    cv
    #
    wf
    #
    @13
    @13
    @35
    cfv
    #
    @3
    @4
    co
    #
    wceq
    #
    vb
    @10
    wral
    #
    wa
    #
    @9
    vf
    @33
    @41
    vf
    wex
    #
    @0
    @32
    @16
    @42
    @12
    @14
    @39
    vb
    vx
    @10
    cX
    vf
    @2
    @37
    wceq
    #
    @5
    @38
    @13
    @2
    @37
    @3
    @4
    oveq1
    #
    eqeq2d
    ac6sfi
    adantrl
    adantl
    @34
    @41
    wa
    #
    @35
    crn
    #
    @8
    wcel
    #
    cY
    vx
    @46
    @5
    ciun
    #
    wss
    #
    @9
    @45
    @46
    cX
    wss
    #
    @46
    cfn
    wcel
    #
    @47
    @36
    @50
    @34
    @40
    @10
    cX
    @35
    frn
    ad2antrl
    @45
    @32
    @10
    @46
    @35
    wfo
    #
    @51
    @0
    @32
    @17
    @41
    simplrl
    @45
    @35
    @10
    wfn
    #
    @52
    @36
    @53
    @34
    @40
    @10
    cX
    @35
    ffn
    ad2antrl
    #
    @10
    @35
    dffn4
    sylib
    @10
    @46
    @35
    fofi
    syl2anc
    @46
    cX
    elfpw
    sylanbrc
    @45
    cY
    vb
    @10
    @38
    ciun
    #
    @48
    @45
    cY
    @11
    @55
    @34
    @12
    @41
    @0
    @32
    @12
    @16
    simprrl
    adantr
    @40
    @11
    @55
    wceq
    @34
    @36
    @40
    @11
    vb
    @10
    @13
    ciun
    @55
    vb
    @10
    uniiun
    vb
    @10
    @13
    @38
    iuneq2
    syl5eq
    ad2antll
    sseqtrd
    @45
    @53
    @48
    @55
    wceq
    @54
    @53
    vy
    @48
    @55
    @53
    vy
    cv
    #
    @5
    wcel
    #
    vx
    @46
    wrex
    @56
    @38
    wcel
    #
    vb
    @10
    wrex
    @56
    @48
    wcel
    @56
    @55
    wcel
    @57
    @58
    vx
    vb
    @10
    @35
    @43
    @5
    @38
    @56
    @44
    eleq2d
    rexrn
    vx
    @56
    @46
    @5
    eliun
    vb
    @56
    @10
    @38
    eliun
    3bitr4g
    eqrdv
    syl
    sseqtr4d
    @7
    @49
    vu
    @46
    @8
    @1
    @46
    wceq
    @6
    @48
    cY
    vx
    @1
    @46
    @5
    iuneq1
    sseq2d
    rspcev
    syl2anc
    exlimddv
    rexlimdvaa
    impbid
    ralbidv
    bitrd
end
