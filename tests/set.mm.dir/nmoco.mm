include "cnghm.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cmul.mm"
include "ccom.mm"
include "cnm.mm"
include "cbs.mm"
include "c0g.mm"
include "eqid.mm"
include "cngp.mm"
include "nghmrcl1.mm"
include "adantl.mm"
include "nghmrcl2.mm"
include "adantr.mm"
include "cghm.mm"
include "nghmghm.mm"
include "ghmco.mm"
include "syl2an.mm"
include "cr.mm"
include "nghmcl.mm"
include "remulcl.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "nmoge0.mm"
include "syl3anc.mm"
include "jca.mm"
include "mulge0.mm"
include "cv.mm"
include "wne.mm"
include "ad2antrr.mm"
include "wf.mm"
include "ghmf.mm"
include "syl.mm"
include "ad2antlr.mm"
include "simprl.mm"
include "ffvelrnd.mm"
include "nmcl.mm"
include "syl2anc.mm"
include "remulcld.mm"
include "sylan.mm"
include "ad2ant2lr.mm"
include "simpll.mm"
include "nmoi.mm"
include "lemul2a.mm"
include "syl31anc.mm"
include "letrd.mm"
include "wceq.mm"
include "fvco3.mm"
include "fveq2d.mm"
include "recnd.mm"
include "mulassd.mm"
include "3brtr4d.mm"
include "nmolb2d.mm"

theorem nmoco
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cG: class G
  let cL: class L
  let cM: class M
  let cN: class N
  let vx: setvar x
  assume nmoco.1: |- N = ( S normOp U )
  assume nmoco.2: |- L = ( T normOp U )
  assume nmoco.3: |- M = ( S normOp T )


  assert |- ( ( F e. ( T NGHom U ) /\ G e. ( S NGHom T ) ) -> ( N ` ( F o. G ) ) <_ ( ( L ` F ) x. ( M ` G ) ) )

  proof
    cF
    cT
    cU
    cnghm
    co
    wcel
    #
    cG
    cS
    cT
    cnghm
    co
    wcel
    #
    wa
    #
    vx
    cF
    cL
    cfv
    #
    cG
    cM
    cfv
    #
    cmul
    co
    #
    cS
    cU
    cF
    cG
    ccom
    #
    cS
    cnm
    cfv
    #
    cU
    cnm
    cfv
    #
    cN
    cS
    cbs
    cfv
    #
    cS
    c0g
    cfv
    #
    nmoco.1
    @9
    eqid
    #
    @7
    eqid
    #
    @8
    eqid
    #
    @10
    eqid
    @1
    cS
    cngp
    wcel
    #
    @0
    cS
    cT
    cG
    nghmrcl1
    #
    adantl
    @0
    cU
    cngp
    wcel
    #
    @1
    cT
    cU
    cF
    nghmrcl2
    #
    adantr
    @0
    cF
    cT
    cU
    cghm
    co
    wcel
    #
    cG
    cS
    cT
    cghm
    co
    wcel
    #
    @6
    cS
    cU
    cghm
    co
    wcel
    @1
    cT
    cU
    cF
    nghmghm
    #
    cS
    cT
    cG
    nghmghm
    #
    cS
    cT
    cU
    cF
    cG
    ghmco
    syl2an
    @0
    @3
    cr
    wcel
    #
    @4
    cr
    wcel
    #
    @5
    cr
    wcel
    @1
    cT
    cU
    cF
    cL
    nmoco.2
    nghmcl
    #
    cS
    cT
    cG
    cM
    nmoco.3
    nghmcl
    #
    @3
    @4
    remulcl
    syl2an
    @0
    @22
    cc0
    @3
    cle
    wbr
    #
    wa
    #
    @23
    cc0
    @4
    cle
    wbr
    #
    wa
    cc0
    @5
    cle
    wbr
    @1
    @0
    @22
    @26
    @24
    @0
    cT
    cngp
    wcel
    #
    @16
    @18
    @26
    cT
    cU
    cF
    nghmrcl1
    #
    @17
    @20
    cT
    cU
    cF
    cL
    nmoco.2
    nmoge0
    syl3anc
    jca
    #
    @1
    @23
    @28
    @25
    @1
    @14
    @29
    @19
    @28
    @15
    cS
    cT
    cG
    nghmrcl2
    @21
    cS
    cT
    cG
    cM
    nmoco.3
    nmoge0
    syl3anc
    jca
    @3
    @4
    mulge0
    syl2an
    @2
    vx
    cv
    #
    @9
    wcel
    #
    @32
    @10
    wne
    #
    wa
    #
    wa
    #
    @32
    cG
    cfv
    #
    cF
    cfv
    #
    @8
    cfv
    #
    @3
    @4
    @32
    @7
    cfv
    #
    cmul
    co
    #
    cmul
    co
    #
    @32
    @6
    cfv
    #
    @8
    cfv
    @5
    @40
    cmul
    co
    cle
    @36
    @39
    @3
    @37
    cT
    cnm
    cfv
    #
    cfv
    #
    cmul
    co
    #
    @42
    @36
    @16
    @38
    cU
    cbs
    cfv
    #
    wcel
    @39
    cr
    wcel
    @0
    @16
    @1
    @35
    @17
    ad2antrr
    @36
    cT
    cbs
    cfv
    #
    @47
    @37
    cF
    @36
    @18
    @48
    @47
    cF
    wf
    @0
    @18
    @1
    @35
    @20
    ad2antrr
    cT
    cU
    cF
    @48
    @47
    @48
    eqid
    #
    @47
    eqid
    #
    ghmf
    syl
    @36
    @9
    @48
    @32
    cG
    @36
    @19
    @9
    @48
    cG
    wf
    #
    @1
    @19
    @0
    @35
    @21
    ad2antlr
    cS
    cT
    cG
    @9
    @48
    @11
    @49
    ghmf
    syl
    #
    @2
    @33
    @34
    simprl
    #
    ffvelrnd
    #
    ffvelrnd
    @38
    cU
    @8
    @47
    @50
    @13
    nmcl
    syl2anc
    @36
    @3
    @45
    @0
    @22
    @1
    @35
    @24
    ad2antrr
    #
    @36
    @29
    @37
    @48
    wcel
    #
    @45
    cr
    wcel
    #
    @0
    @29
    @1
    @35
    @30
    ad2antrr
    @54
    @37
    cT
    @44
    @48
    @49
    @44
    eqid
    #
    nmcl
    syl2anc
    #
    remulcld
    @36
    @3
    @41
    @55
    @36
    @4
    @40
    @1
    @23
    @0
    @35
    @25
    ad2antlr
    #
    @1
    @33
    @40
    cr
    wcel
    #
    @0
    @34
    @1
    @14
    @33
    @61
    @15
    @32
    cS
    @7
    @9
    @11
    @12
    nmcl
    sylan
    ad2ant2lr
    #
    remulcld
    #
    remulcld
    @36
    @0
    @56
    @39
    @46
    cle
    wbr
    @0
    @1
    @35
    simpll
    @54
    cT
    cU
    cF
    @44
    @8
    cL
    @48
    @37
    nmoco.2
    @49
    @58
    @13
    nmoi
    syl2anc
    @36
    @57
    @41
    cr
    wcel
    @27
    @45
    @41
    cle
    wbr
    #
    @46
    @42
    cle
    wbr
    @59
    @63
    @0
    @27
    @1
    @35
    @31
    ad2antrr
    @1
    @33
    @64
    @0
    @34
    cS
    cT
    cG
    @7
    @44
    cM
    @9
    @32
    nmoco.3
    @11
    @12
    @58
    nmoi
    ad2ant2lr
    @45
    @41
    @3
    lemul2a
    syl31anc
    letrd
    @36
    @43
    @38
    @8
    @36
    @51
    @33
    @43
    @38
    wceq
    @52
    @53
    @9
    @48
    @32
    cF
    cG
    fvco3
    syl2anc
    fveq2d
    @36
    @3
    @4
    @40
    @36
    @3
    @55
    recnd
    @36
    @4
    @60
    recnd
    @36
    @40
    @62
    recnd
    mulassd
    3brtr4d
    nmolb2d
end
