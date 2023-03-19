include "cv.mm"
include "cfv.mm"
include "cneg.mm"
include "cmpt.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "cc0.mm"
include "cmin.mm"
include "co.mm"
include "cr.mm"
include "ctop.mm"
include "wcel.mm"
include "ctopon.mm"
include "ccmp.mm"
include "cmptop.mm"
include "syl.mm"
include "toptopon.mm"
include "sylib.mm"
include "ccn.mm"
include "wf.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cuni.mm"
include "uniretop.mm"
include "unieqi.mm"
include "eqtr4i.mm"
include "cnf.mm"
include "feqmptd.mm"
include "eqeltrrd.mm"
include "retopon.mm"
include "eqeltri.mm"
include "a1i.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "crest.mm"
include "cc.mm"
include "eqid.mm"
include "cnfldtopon.mm"
include "0cnd.mm"
include "cnmptc.mm"
include "tgioo2.mm"
include "eqtri.mm"
include "wss.mm"
include "ax-resscn.mm"
include "cnmptid.mm"
include "cnmpt1res.mm"
include "ctx.mm"
include "subcn.mm"
include "cnmpt12f.mm"
include "wb.mm"
include "df-neg.mm"
include "renegcl.mm"
include "syl5eqelr.mm"
include "adantl.mm"
include "fmptd.mm"
include "frn.mm"
include "cnrest2.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "oveq2i.mm"
include "syl6eleqr.mm"
include "wceq.mm"
include "negeq.mm"
include "syl5eqr.mm"
include "cnmpt11.mm"
include "evth.mm"
include "wa.mm"
include "fveq2.mm"
include "negeqd.mm"
include "negex.mm"
include "fvmpt.mm"
include "ad2antlr.mm"
include "breq12d.mm"
include "ffvelrnda.mm"
include "adantr.mm"
include "adantlr.mm"
include "lenegd.mm"
include "bitr4d.mm"
include "ralbidva.mm"
include "rexbidva.mm"

theorem evth2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let vu: setvar u
  let vv: setvar v
  let vz: setvar z
  let vw: setvar w
  assume bndth.1: |- X = U. J
  assume bndth.2: |- K = ( topGen ` ran (,) )
  assume bndth.3: |- ( ph -> J e. Comp )
  assume bndth.4: |- ( ph -> F e. ( J Cn K ) )
  assume evth.5: |- ( ph -> X =/= (/) )

  disjoint x y
  disjoint F x
  disjoint F y
  disjoint K y
  disjoint ph x
  disjoint ph y
  disjoint X x
  disjoint X y
  disjoint J x
  disjoint J y
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint F u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint F v
  disjoint x z
  disjoint y z
  disjoint F z
  disjoint K u
  disjoint K v
  disjoint K z
  disjoint u w
  disjoint ph u
  disjoint v w
  disjoint ph v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint ph w
  disjoint ph z
  disjoint X v
  disjoint X z
  disjoint J z
  assert |- ( ph -> E. x e. X A. y e. X ( F ` x ) <_ ( F ` y ) )

  proof
    wph
    vy
    cv
    #
    vz
    cX
    vz
    cv
    #
    cF
    cfv
    #
    cneg
    #
    cmpt
    #
    cfv
    #
    vx
    cv
    #
    @4
    cfv
    #
    cle
    wbr
    #
    vy
    cX
    wral
    #
    vx
    cX
    wrex
    @6
    cF
    cfv
    #
    @0
    cF
    cfv
    #
    cle
    wbr
    #
    vy
    cX
    wral
    #
    vx
    cX
    wrex
    wph
    vx
    vy
    @4
    cJ
    cK
    cX
    bndth.1
    bndth.2
    bndth.3
    wph
    vz
    vy
    @2
    cc0
    @0
    cmin
    co
    #
    @3
    cJ
    cK
    cK
    cX
    cr
    wph
    cJ
    ctop
    wcel
    #
    cJ
    cX
    ctopon
    cfv
    wcel
    wph
    cJ
    ccmp
    wcel
    @15
    bndth.3
    cJ
    cmptop
    syl
    cJ
    cX
    bndth.1
    toptopon
    sylib
    wph
    cF
    vz
    cX
    @2
    cmpt
    cJ
    cK
    ccn
    co
    #
    wph
    vz
    cX
    cr
    cF
    wph
    cF
    @16
    wcel
    cX
    cr
    cF
    wf
    bndth.4
    cF
    cJ
    cK
    cX
    cr
    bndth.1
    cr
    cioo
    crn
    ctg
    cfv
    #
    cuni
    cK
    cuni
    uniretop
    cK
    @17
    bndth.2
    unieqi
    eqtr4i
    cnf
    syl
    #
    feqmptd
    bndth.4
    eqeltrrd
    cK
    cr
    ctopon
    cfv
    #
    wcel
    wph
    cK
    @17
    @19
    bndth.2
    retopon
    eqeltri
    a1i
    #
    wph
    vy
    cr
    @14
    cmpt
    #
    cK
    ccnfld
    ctopn
    cfv
    #
    cr
    crest
    co
    #
    ccn
    co
    #
    cK
    cK
    ccn
    co
    wph
    @21
    cK
    @22
    ccn
    co
    wcel
    #
    @21
    @24
    wcel
    #
    wph
    vy
    cc0
    @0
    cmin
    cK
    @22
    @22
    @22
    cr
    @20
    wph
    vy
    cc0
    cK
    @22
    cr
    cc
    @20
    @22
    cc
    ctopon
    cfv
    wcel
    #
    wph
    @22
    @22
    eqid
    #
    cnfldtopon
    a1i
    #
    wph
    0cnd
    cnmptc
    wph
    vy
    @0
    @22
    cK
    @22
    cc
    cr
    cK
    @17
    @23
    bndth.2
    @22
    @28
    tgioo2
    eqtri
    #
    @29
    cr
    cc
    wss
    #
    wph
    ax-resscn
    a1i
    #
    wph
    vy
    @22
    cc
    @29
    cnmptid
    cnmpt1res
    cmin
    @22
    @22
    ctx
    co
    @22
    ccn
    co
    wcel
    wph
    @22
    @28
    subcn
    a1i
    cnmpt12f
    wph
    @27
    @21
    crn
    cr
    wss
    #
    @31
    @25
    @26
    wb
    @29
    wph
    cr
    cr
    @21
    wf
    @33
    wph
    vy
    cr
    @14
    cr
    @21
    @0
    cr
    wcel
    #
    @14
    cr
    wcel
    wph
    @34
    @14
    @0
    cneg
    #
    cr
    @0
    df-neg
    #
    @0
    renegcl
    syl5eqelr
    adantl
    @21
    eqid
    fmptd
    cr
    cr
    @21
    frn
    syl
    @32
    cr
    @21
    cK
    @22
    cc
    cnrest2
    syl3anc
    mpbid
    cK
    @23
    cK
    ccn
    @30
    oveq2i
    syl6eleqr
    @0
    @2
    wceq
    @14
    @35
    @3
    @36
    @0
    @2
    negeq
    syl5eqr
    cnmpt11
    evth.5
    evth
    wph
    @9
    @13
    vx
    cX
    wph
    @6
    cX
    wcel
    #
    wa
    #
    @8
    @12
    vy
    cX
    @38
    @0
    cX
    wcel
    #
    wa
    #
    @8
    @11
    cneg
    #
    @10
    cneg
    #
    cle
    wbr
    @12
    @40
    @5
    @41
    @7
    @42
    cle
    @39
    @5
    @41
    wceq
    @38
    vz
    @0
    @3
    @41
    cX
    @4
    @1
    @0
    wceq
    @2
    @11
    @1
    @0
    cF
    fveq2
    negeqd
    @4
    eqid
    #
    @11
    negex
    fvmpt
    adantl
    @37
    @7
    @42
    wceq
    wph
    @39
    vz
    @6
    @3
    @42
    cX
    @4
    @1
    @6
    wceq
    @2
    @10
    @1
    @6
    cF
    fveq2
    negeqd
    @43
    @10
    negex
    fvmpt
    ad2antlr
    breq12d
    @40
    @10
    @11
    @38
    @10
    cr
    wcel
    @39
    wph
    cX
    cr
    @6
    cF
    @18
    ffvelrnda
    adantr
    wph
    @39
    @11
    cr
    wcel
    @37
    wph
    cX
    cr
    @0
    cF
    @18
    ffvelrnda
    adantlr
    lenegd
    bitr4d
    ralbidva
    rexbidva
    mpbid
end
