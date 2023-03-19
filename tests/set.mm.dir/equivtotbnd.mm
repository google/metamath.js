include "cme.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "cbl.mm"
include "co.mm"
include "ciun.mm"
include "wceq.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "crp.mm"
include "wral.mm"
include "ctotbnd.mm"
include "wa.mm"
include "cdiv.mm"
include "simpr.mm"
include "adantr.mm"
include "rpdivcld.mm"
include "istotbnd3.mm"
include "simprbi.mm"
include "syl.mm"
include "oveq2.mm"
include "iuneq2d.mm"
include "eqeq1d.mm"
include "rexbidv.mm"
include "rspcv.mm"
include "sylc.mm"
include "wss.mm"
include "elfpw.mm"
include "simplbi.mm"
include "adantl.mm"
include "sselda.mm"
include "cmopn.mm"
include "eqid.mm"
include "metss2lem.mm"
include "anass1rs.mm"
include "adantlr.mm"
include "syldan.mm"
include "ralrimiva.mm"
include "ss2iun.mm"
include "sseq1.mm"
include "syl5ibcom.mm"
include "cxmt.mm"
include "cxr.mm"
include "ad3antrrr.mm"
include "metxmet.mm"
include "simpllr.mm"
include "rpxrd.mm"
include "blssm.mm"
include "syl3anc.mm"
include "iunss.mm"
include "sylibr.mm"
include "jctild.mm"
include "eqss.mm"
include "syl6ibr.mm"
include "reximdva.mm"
include "mpd.mm"
include "sylanbrc.mm"

theorem equivtotbnd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cR: class R
  let cM: class M
  let cN: class N
  let cX: class X
  let vs: setvar s
  let vv: setvar v
  let vr: setvar r
  assume equivtotbnd.1: |- ( ph -> M e. ( TotBnd ` X ) )
  assume equivtotbnd.2: |- ( ph -> N e. ( Met ` X ) )
  assume equivtotbnd.3: |- ( ph -> R e. RR+ )
  assume equivtotbnd.4: |- ( ( ph /\ ( x e. X /\ y e. X ) ) -> ( x N y ) <_ ( R x. ( x M y ) ) )

  disjoint x y
  disjoint M x
  disjoint M y
  disjoint N x
  disjoint N y
  disjoint ph x
  disjoint ph y
  disjoint X x
  disjoint X y
  disjoint R x
  disjoint R y
  disjoint s v
  disjoint s x
  disjoint s y
  disjoint M s
  disjoint v x
  disjoint v y
  disjoint M v
  disjoint r v
  disjoint r x
  disjoint r y
  disjoint N r
  disjoint N v
  disjoint ph r
  disjoint ph v
  disjoint r s
  disjoint X r
  disjoint X s
  disjoint X v
  disjoint R s
  disjoint R v
  assert |- ( ph -> N e. ( TotBnd ` X ) )

  proof
    wph
    cN
    cX
    cme
    cfv
    #
    wcel
    #
    vx
    vv
    cv
    #
    vx
    cv
    #
    vr
    cv
    #
    cN
    cbl
    cfv
    co
    #
    ciun
    #
    cX
    wceq
    #
    vv
    cX
    cpw
    cfn
    cin
    #
    wrex
    #
    vr
    crp
    wral
    cN
    cX
    ctotbnd
    cfv
    #
    wcel
    equivtotbnd.2
    wph
    @9
    vr
    crp
    wph
    @4
    crp
    wcel
    #
    wa
    #
    vx
    @2
    @3
    @4
    cR
    cdiv
    co
    #
    cM
    cbl
    cfv
    #
    co
    #
    ciun
    #
    cX
    wceq
    #
    vv
    @8
    wrex
    #
    @9
    @12
    @13
    crp
    wcel
    vx
    @2
    @3
    vs
    cv
    #
    @14
    co
    #
    ciun
    #
    cX
    wceq
    #
    vv
    @8
    wrex
    #
    vs
    crp
    wral
    #
    @18
    @12
    @4
    cR
    wph
    @11
    simpr
    wph
    cR
    crp
    wcel
    @11
    equivtotbnd.3
    adantr
    rpdivcld
    @12
    cM
    @10
    wcel
    #
    @24
    wph
    @25
    @11
    equivtotbnd.1
    adantr
    @25
    cM
    @0
    wcel
    #
    @24
    vx
    vv
    cM
    cX
    vs
    istotbnd3
    #
    simprbi
    syl
    @23
    @18
    vs
    @13
    crp
    @19
    @13
    wceq
    #
    @22
    @17
    vv
    @8
    @28
    @21
    @16
    cX
    @28
    vx
    @2
    @20
    @15
    @19
    @13
    @3
    @14
    oveq2
    iuneq2d
    eqeq1d
    rexbidv
    rspcv
    sylc
    @12
    @17
    @7
    vv
    @8
    @12
    @2
    @8
    wcel
    #
    wa
    #
    @17
    @6
    cX
    wss
    #
    cX
    @6
    wss
    #
    wa
    @7
    @30
    @17
    @32
    @31
    @30
    @16
    @6
    wss
    #
    @17
    @32
    @30
    @15
    @5
    wss
    #
    vx
    @2
    wral
    @33
    @30
    @34
    vx
    @2
    @30
    @3
    @2
    wcel
    #
    @3
    cX
    wcel
    #
    @34
    @30
    @2
    cX
    @3
    @29
    @2
    cX
    wss
    #
    @12
    @29
    @37
    @2
    cfn
    wcel
    @2
    cX
    elfpw
    simplbi
    adantl
    sselda
    #
    @12
    @36
    @34
    @29
    wph
    @36
    @11
    @34
    wph
    vx
    vy
    cN
    cM
    cR
    @4
    cN
    cmopn
    cfv
    #
    cM
    cmopn
    cfv
    #
    cX
    @39
    eqid
    @40
    eqid
    equivtotbnd.2
    wph
    @25
    @26
    equivtotbnd.1
    @25
    @26
    @24
    @27
    simplbi
    syl
    equivtotbnd.3
    equivtotbnd.4
    metss2lem
    anass1rs
    adantlr
    syldan
    ralrimiva
    vx
    @2
    @15
    @5
    ss2iun
    syl
    @16
    cX
    @6
    sseq1
    syl5ibcom
    @30
    @5
    cX
    wss
    #
    vx
    @2
    wral
    @31
    @30
    @41
    vx
    @2
    @30
    @35
    wa
    #
    cN
    cX
    cxmt
    cfv
    wcel
    #
    @36
    @4
    cxr
    wcel
    @41
    @42
    @1
    @43
    wph
    @1
    @11
    @29
    @35
    equivtotbnd.2
    ad3antrrr
    cN
    cX
    metxmet
    syl
    @38
    @42
    @4
    wph
    @11
    @29
    @35
    simpllr
    rpxrd
    cN
    @3
    @4
    cX
    blssm
    syl3anc
    ralrimiva
    vx
    @2
    @5
    cX
    iunss
    sylibr
    jctild
    @6
    cX
    eqss
    syl6ibr
    reximdva
    mpd
    ralrimiva
    vx
    vv
    cN
    cX
    vr
    istotbnd3
    sylanbrc
end
