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
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "crab.mm"
include "cfn.mm"
include "cpw.mm"
include "wrex.mm"
include "crp.mm"
include "wral.mm"
include "sstotbnd2.mm"
include "elin.mm"
include "rabfi.mm"
include "anim2i.mm"
include "sylbi.mm"
include "ancoms.mm"
include "an12.mm"
include "sylib.mm"
include "reximi2.mm"
include "ralimi.mm"
include "syl6bi.mm"
include "ssrab2.mm"
include "elpwi.mm"
include "ad2antlr.mm"
include "syl5ss.mm"
include "simprr.mm"
include "elfpw.mm"
include "sylanbrc.mm"
include "ssel2.mm"
include "eliun.mm"
include "inelcm.mm"
include "expcom.mm"
include "ancrd.mm"
include "reximdv.mm"
include "impcom.mm"
include "sylancom.mm"
include "wceq.mm"
include "oveq1.mm"
include "eleq2d.mm"
include "rexrab2.mm"
include "bitri.mm"
include "sylibr.mm"
include "ex.mm"
include "ssrdv.mm"
include "ad2antrl.mm"
include "iuneq1.mm"
include "sseq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "rexlimdva.mm"
include "ralimdv.mm"
include "sylibrd.mm"
include "impbid.mm"

theorem sstotbnd3
  let vx: setvar x
  let vv: setvar v
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y
  let vd: setvar d
  let vb: setvar b
  let vc: setvar c
  let vf: setvar f
  let vu: setvar u
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume sstotbnd.2: |- N = ( M |` ( Y X. Y ) )

  disjoint d v
  disjoint d x
  disjoint M d
  disjoint v x
  disjoint M v
  disjoint M x
  disjoint X d
  disjoint X v
  disjoint X x
  disjoint N d
  disjoint N v
  disjoint N x
  disjoint Y d
  disjoint Y v
  disjoint Y x
  disjoint b c
  disjoint b d
  disjoint b f
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint M b
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
  disjoint X b
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
  disjoint Y b
  disjoint Y c
  disjoint Y f
  disjoint Y u
  disjoint Y w
  disjoint Y y
  disjoint Y z
  assert |- ( ( M e. ( Met ` X ) /\ Y C_ X ) -> ( N e. ( TotBnd ` Y ) <-> A. d e. RR+ E. v e. ~P X ( Y C_ U_ x e. v ( x ( ball ` M ) d ) /\ { x e. v | ( ( x ( ball ` M ) d ) i^i Y ) =/= (/) } e. Fin ) ) )

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
    #
    cY
    vx
    vv
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
    @6
    cY
    cin
    c0
    wne
    #
    vx
    @2
    crab
    #
    cfn
    wcel
    #
    wa
    #
    vv
    cX
    cpw
    #
    wrex
    #
    vd
    crp
    wral
    #
    @0
    @1
    @8
    vv
    @13
    cfn
    cin
    #
    wrex
    #
    vd
    crp
    wral
    @15
    vx
    vv
    cM
    cN
    cX
    cY
    vd
    sstotbnd.2
    sstotbnd2
    @17
    @14
    vd
    crp
    @8
    @12
    vv
    @16
    @13
    @2
    @16
    wcel
    #
    @8
    wa
    @8
    @2
    @13
    wcel
    #
    @11
    wa
    #
    wa
    #
    @19
    @12
    wa
    @8
    @18
    @21
    @18
    @20
    @8
    @18
    @19
    @2
    cfn
    wcel
    #
    wa
    @20
    @2
    @13
    cfn
    elin
    @22
    @11
    @19
    @9
    vx
    @2
    rabfi
    anim2i
    sylbi
    anim2i
    ancoms
    @8
    @19
    @11
    an12
    sylib
    reximi2
    ralimi
    syl6bi
    @0
    @15
    cY
    vy
    vw
    cv
    #
    vy
    cv
    #
    @4
    @5
    co
    #
    ciun
    #
    wss
    #
    vw
    @16
    wrex
    #
    vd
    crp
    wral
    @1
    @0
    @14
    @28
    vd
    crp
    @0
    @12
    @28
    vv
    @13
    @0
    @19
    wa
    #
    @12
    @28
    @29
    @12
    wa
    #
    @10
    @16
    wcel
    #
    cY
    vy
    @10
    @25
    ciun
    #
    wss
    #
    @28
    @30
    @10
    cX
    wss
    @11
    @31
    @30
    @10
    @2
    cX
    @9
    vx
    @2
    ssrab2
    @19
    @2
    cX
    wss
    @0
    @12
    @2
    cX
    elpwi
    ad2antlr
    syl5ss
    @29
    @8
    @11
    simprr
    @10
    cX
    elfpw
    sylanbrc
    @8
    @33
    @29
    @11
    @8
    vz
    cY
    @32
    @8
    vz
    cv
    #
    cY
    wcel
    #
    @34
    @32
    wcel
    #
    @8
    @35
    wa
    #
    @9
    @34
    @6
    wcel
    #
    wa
    #
    vx
    @2
    wrex
    #
    @36
    @8
    @35
    @38
    vx
    @2
    wrex
    #
    @40
    @37
    @34
    @7
    wcel
    @41
    cY
    @7
    @34
    ssel2
    vx
    @34
    @2
    @6
    eliun
    sylib
    @35
    @41
    @40
    @35
    @38
    @39
    vx
    @2
    @35
    @38
    @9
    @38
    @35
    @9
    @34
    @6
    cY
    inelcm
    expcom
    ancrd
    reximdv
    impcom
    sylancom
    @36
    @34
    @25
    wcel
    #
    vy
    @10
    wrex
    @40
    vy
    @34
    @10
    @25
    eliun
    @9
    @42
    @38
    vy
    vx
    @2
    @24
    @3
    wceq
    @25
    @6
    @34
    @24
    @3
    @4
    @5
    oveq1
    eleq2d
    rexrab2
    bitri
    sylibr
    ex
    ssrdv
    ad2antrl
    @27
    @33
    vw
    @10
    @16
    @23
    @10
    wceq
    @26
    @32
    cY
    vy
    @23
    @10
    @25
    iuneq1
    sseq2d
    rspcev
    syl2anc
    ex
    rexlimdva
    ralimdv
    vy
    vw
    cM
    cN
    cX
    cY
    vd
    sstotbnd.2
    sstotbnd2
    sylibrd
    impbid
end
