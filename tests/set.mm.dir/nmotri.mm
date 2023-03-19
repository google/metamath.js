include "cabl.mm"
include "wcel.mm"
include "cnghm.mm"
include "co.mm"
include "w3a.mm"
include "cfv.mm"
include "caddc.mm"
include "cof.mm"
include "cnm.mm"
include "cbs.mm"
include "c0g.mm"
include "eqid.mm"
include "cngp.mm"
include "nghmrcl1.mm"
include "3ad2ant2.mm"
include "nghmrcl2.mm"
include "cghm.mm"
include "id.mm"
include "nghmghm.mm"
include "ghmplusg.mm"
include "syl3an.mm"
include "cr.mm"
include "nghmcl.mm"
include "3ad2ant3.mm"
include "readdcld.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "nmoge0.mm"
include "syl3anc.mm"
include "addge0d.mm"
include "cv.mm"
include "wne.mm"
include "wa.mm"
include "cmul.mm"
include "adantr.mm"
include "cgrp.mm"
include "ngpgrp.mm"
include "syl.mm"
include "wf.mm"
include "ghmf.mm"
include "simprl.mm"
include "ffvelrnd.mm"
include "grpcl.mm"
include "nmcl.mm"
include "syl2anc.mm"
include "simpl.mm"
include "syl2an.mm"
include "remulcld.mm"
include "nmtri.mm"
include "simpl2.mm"
include "nmoi.mm"
include "simpl3.mm"
include "le2addd.mm"
include "letrd.mm"
include "wfn.mm"
include "cvv.mm"
include "wceq.mm"
include "ffn.mm"
include "fvexd.mm"
include "fnfvof.mm"
include "syl22anc.mm"
include "fveq2d.mm"
include "recnd.mm"
include "adddird.mm"
include "3brtr4d.mm"
include "nmolb2d.mm"

theorem nmotri
  let c.pl: class .+
  let cS: class S
  let cT: class T
  let cF: class F
  let cG: class G
  let cN: class N
  let vx: setvar x
  assume nmotri.1: |- N = ( S normOp T )
  assume nmotri.p: |- .+ = ( +g ` T )


  assert |- ( ( T e. Abel /\ F e. ( S NGHom T ) /\ G e. ( S NGHom T ) ) -> ( N ` ( F oF .+ G ) ) <_ ( ( N ` F ) + ( N ` G ) ) )

  proof
    cT
    cabl
    wcel
    #
    cF
    cS
    cT
    cnghm
    co
    #
    wcel
    #
    cG
    @1
    wcel
    #
    w3a
    #
    vx
    cF
    cN
    cfv
    #
    cG
    cN
    cfv
    #
    caddc
    co
    #
    cS
    cT
    cF
    cG
    c.pl
    cof
    co
    #
    cS
    cnm
    cfv
    #
    cT
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
    nmotri.1
    @11
    eqid
    #
    @9
    eqid
    #
    @10
    eqid
    #
    @12
    eqid
    @2
    @0
    cS
    cngp
    wcel
    #
    @3
    cS
    cT
    cF
    nghmrcl1
    3ad2ant2
    #
    @2
    @0
    cT
    cngp
    wcel
    #
    @3
    cS
    cT
    cF
    nghmrcl2
    3ad2ant2
    #
    @0
    @0
    @2
    cF
    cS
    cT
    cghm
    co
    #
    wcel
    #
    @3
    cG
    @20
    wcel
    #
    @8
    @20
    wcel
    @0
    id
    cS
    cT
    cF
    nghmghm
    #
    cS
    cT
    cG
    nghmghm
    #
    c.pl
    cF
    cG
    cS
    cT
    nmotri.p
    ghmplusg
    syl3an
    @4
    @5
    @6
    @2
    @0
    @5
    cr
    wcel
    #
    @3
    cS
    cT
    cF
    cN
    nmotri.1
    nghmcl
    3ad2ant2
    #
    @3
    @0
    @6
    cr
    wcel
    #
    @2
    cS
    cT
    cG
    cN
    nmotri.1
    nghmcl
    3ad2ant3
    #
    readdcld
    @4
    @5
    @6
    @26
    @28
    @4
    @16
    @18
    @21
    cc0
    @5
    cle
    wbr
    @17
    @19
    @2
    @0
    @21
    @3
    @23
    3ad2ant2
    #
    cS
    cT
    cF
    cN
    nmotri.1
    nmoge0
    syl3anc
    @4
    @16
    @18
    @22
    cc0
    @6
    cle
    wbr
    @17
    @19
    @3
    @0
    @22
    @2
    @24
    3ad2ant3
    #
    cS
    cT
    cG
    cN
    nmotri.1
    nmoge0
    syl3anc
    addge0d
    @4
    vx
    cv
    #
    @11
    wcel
    #
    @31
    @12
    wne
    #
    wa
    #
    wa
    #
    @31
    cF
    cfv
    #
    @31
    cG
    cfv
    #
    c.pl
    co
    #
    @10
    cfv
    #
    @5
    @31
    @9
    cfv
    #
    cmul
    co
    #
    @6
    @40
    cmul
    co
    #
    caddc
    co
    #
    @31
    @8
    cfv
    #
    @10
    cfv
    @7
    @40
    cmul
    co
    cle
    @35
    @39
    @36
    @10
    cfv
    #
    @37
    @10
    cfv
    #
    caddc
    co
    #
    @43
    @35
    @18
    @38
    cT
    cbs
    cfv
    #
    wcel
    #
    @39
    cr
    wcel
    @4
    @18
    @34
    @19
    adantr
    #
    @35
    cT
    cgrp
    wcel
    #
    @36
    @48
    wcel
    #
    @37
    @48
    wcel
    #
    @49
    @35
    @18
    @51
    @50
    cT
    ngpgrp
    syl
    @35
    @11
    @48
    @31
    cF
    @35
    @21
    @11
    @48
    cF
    wf
    #
    @4
    @21
    @34
    @29
    adantr
    cS
    cT
    cF
    @11
    @48
    @13
    @48
    eqid
    #
    ghmf
    syl
    #
    @4
    @32
    @33
    simprl
    #
    ffvelrnd
    #
    @35
    @11
    @48
    @31
    cG
    @35
    @22
    @11
    @48
    cG
    wf
    #
    @4
    @22
    @34
    @30
    adantr
    cS
    cT
    cG
    @11
    @48
    @13
    @55
    ghmf
    syl
    #
    @57
    ffvelrnd
    #
    @48
    c.pl
    cT
    @36
    @37
    @55
    nmotri.p
    grpcl
    syl3anc
    @38
    cT
    @10
    @48
    @55
    @15
    nmcl
    syl2anc
    @35
    @45
    @46
    @35
    @18
    @52
    @45
    cr
    wcel
    @50
    @58
    @36
    cT
    @10
    @48
    @55
    @15
    nmcl
    syl2anc
    #
    @35
    @18
    @53
    @46
    cr
    wcel
    @50
    @61
    @37
    cT
    @10
    @48
    @55
    @15
    nmcl
    syl2anc
    #
    readdcld
    @35
    @41
    @42
    @35
    @5
    @40
    @4
    @25
    @34
    @26
    adantr
    #
    @4
    @16
    @32
    @40
    cr
    wcel
    @34
    @17
    @32
    @33
    simpl
    @31
    cS
    @9
    @11
    @13
    @14
    nmcl
    syl2an
    #
    remulcld
    #
    @35
    @6
    @40
    @4
    @27
    @34
    @28
    adantr
    #
    @65
    remulcld
    #
    readdcld
    @35
    @18
    @52
    @53
    @39
    @47
    cle
    wbr
    @50
    @58
    @61
    @36
    @37
    c.pl
    cT
    @10
    @48
    @55
    @15
    nmotri.p
    nmtri
    syl3anc
    @35
    @45
    @46
    @41
    @42
    @62
    @63
    @66
    @68
    @35
    @2
    @32
    @45
    @41
    cle
    wbr
    @0
    @2
    @3
    @34
    simpl2
    @57
    cS
    cT
    cF
    @9
    @10
    cN
    @11
    @31
    nmotri.1
    @13
    @14
    @15
    nmoi
    syl2anc
    @35
    @3
    @32
    @46
    @42
    cle
    wbr
    @0
    @2
    @3
    @34
    simpl3
    @57
    cS
    cT
    cG
    @9
    @10
    cN
    @11
    @31
    nmotri.1
    @13
    @14
    @15
    nmoi
    syl2anc
    le2addd
    letrd
    @35
    @44
    @38
    @10
    @35
    cF
    @11
    wfn
    #
    cG
    @11
    wfn
    #
    @11
    cvv
    wcel
    @32
    @44
    @38
    wceq
    @35
    @54
    @69
    @56
    @11
    @48
    cF
    ffn
    syl
    @35
    @59
    @70
    @60
    @11
    @48
    cG
    ffn
    syl
    @35
    cS
    cbs
    fvexd
    @57
    @11
    c.pl
    cF
    cG
    cvv
    @31
    fnfvof
    syl22anc
    fveq2d
    @35
    @5
    @6
    @40
    @35
    @5
    @64
    recnd
    @35
    @6
    @67
    recnd
    @35
    @40
    @65
    recnd
    adddird
    3brtr4d
    nmolb2d
end
