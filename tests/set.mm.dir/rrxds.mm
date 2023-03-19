include "wcel.mm"
include "cds.mm"
include "cfv.mm"
include "crefld.mm"
include "cfrlm.mm"
include "co.mm"
include "ctch.mm"
include "cnm.mm"
include "csg.mm"
include "ccom.mm"
include "cv.mm"
include "cmin.mm"
include "c2.mm"
include "cexp.mm"
include "cmpt.mm"
include "cgsu.mm"
include "csqrt.mm"
include "cmpt2.mm"
include "rrxval.mm"
include "fveq2d.mm"
include "clmod.mm"
include "cgrp.mm"
include "wceq.mm"
include "crg.mm"
include "csr.mm"
include "recrng.mm"
include "srngring.mm"
include "ax-mp.mm"
include "eqid.mm"
include "frlmlmod.mm"
include "mpan.mm"
include "lmodgrp.mm"
include "tchds.mm"
include "3syl.mm"
include "cxp.mm"
include "wf.mm"
include "cbs.mm"
include "grpsubf.mm"
include "cc0.mm"
include "cfsupp.mm"
include "wbr.mm"
include "cr.mm"
include "cmap.mm"
include "crab.mm"
include "rrxbase.mm"
include "rebase.mm"
include "re0g.mm"
include "frlmbas.mm"
include "eqtrd.mm"
include "sqxpeqd.mm"
include "feq23d.mm"
include "mpbird.mm"
include "fovrnda.mm"
include "wfn.mm"
include "ffn.mm"
include "syl.mm"
include "fnov.mm"
include "sylib.mm"
include "rrxnm.mm"
include "eqtr2d.mm"
include "fveq1.mm"
include "oveq1d.mm"
include "mpteq2dv.mm"
include "oveq2d.mm"
include "fmpt2co.mm"
include "w3a.mm"
include "wa.mm"
include "cof.mm"
include "simp1.mm"
include "simprl.mm"
include "adantr.mm"
include "eleqtrd.mm"
include "3impb.mm"
include "frlmbasmap.mm"
include "syl2anc.mm"
include "elmapi.mm"
include "simprr.mm"
include "inidm.mm"
include "eqidd.mm"
include "offval.mm"
include "a1i.mm"
include "simpl.mm"
include "frlmsubgval.mm"
include "ffvelrnda.mm"
include "resubgval.mm"
include "mpteq2dva.mm"
include "3eqtr4d.mm"
include "resubcld.mm"
include "fvmpt2d.mm"
include "mpt2eq3dva.mm"
include "3eqtr2rd.mm"

theorem rrxds
  let vx: setvar x
  let cB: class B
  let vf: setvar f
  let vg: setvar g
  let cH: class H
  let cI: class I
  let cV: class V
  let vh: setvar h
  let vi: setvar i
  assume rrxval.r: |- H = ( RR^ ` I )
  assume rrxbase.b: |- B = ( Base ` H )

  disjoint f g
  disjoint f x
  disjoint B f
  disjoint g x
  disjoint B g
  disjoint B x
  disjoint I f
  disjoint I g
  disjoint I x
  disjoint V f
  disjoint V g
  disjoint V x
  disjoint f h
  disjoint g h
  disjoint h x
  disjoint B h
  disjoint f i
  disjoint g i
  disjoint h i
  disjoint I h
  disjoint i x
  disjoint I i
  disjoint V h
  assert |- ( I e. V -> ( f e. B , g e. B |-> ( sqrt ` ( RRfld gsum ( x e. I |-> ( ( ( f ` x ) - ( g ` x ) ) ^ 2 ) ) ) ) ) = ( dist ` H ) )

  proof
    cI
    cV
    wcel
    #
    cH
    cds
    cfv
    crefld
    cI
    cfrlm
    co
    #
    ctch
    cfv
    #
    cds
    cfv
    #
    @2
    cnm
    cfv
    #
    @1
    csg
    cfv
    #
    ccom
    #
    vf
    vg
    cB
    cB
    crefld
    vx
    cI
    vx
    cv
    #
    vf
    cv
    #
    cfv
    #
    @7
    vg
    cv
    #
    cfv
    #
    cmin
    co
    #
    c2
    cexp
    co
    #
    cmpt
    #
    cgsu
    co
    #
    csqrt
    cfv
    #
    cmpt2
    #
    @0
    cH
    @2
    cds
    cH
    cI
    cV
    rrxval.r
    rrxval
    #
    fveq2d
    @0
    @1
    clmod
    wcel
    #
    @1
    cgrp
    wcel
    #
    @6
    @3
    wceq
    crefld
    crg
    wcel
    #
    @0
    @19
    crefld
    csr
    wcel
    @21
    recrng
    crefld
    srngring
    ax-mp
    #
    crefld
    @1
    cI
    cV
    @1
    eqid
    #
    frlmlmod
    mpan
    #
    @1
    lmodgrp
    #
    @2
    @5
    @4
    @1
    @2
    eqid
    @4
    eqid
    @5
    eqid
    #
    tchds
    3syl
    @0
    @6
    vf
    vg
    cB
    cB
    crefld
    vx
    cI
    @7
    @8
    @10
    @5
    co
    #
    cfv
    #
    c2
    cexp
    co
    #
    cmpt
    #
    cgsu
    co
    #
    csqrt
    cfv
    #
    cmpt2
    @17
    @0
    vf
    vg
    vh
    cB
    cB
    cB
    @27
    crefld
    vx
    cI
    @7
    vh
    cv
    #
    cfv
    #
    c2
    cexp
    co
    #
    cmpt
    #
    cgsu
    co
    #
    csqrt
    cfv
    #
    @32
    @5
    @4
    @0
    @8
    @10
    cB
    cB
    cB
    @5
    @0
    cB
    cB
    cxp
    #
    cB
    @5
    wf
    #
    @1
    cbs
    cfv
    #
    @41
    cxp
    #
    @41
    @5
    wf
    #
    @0
    @19
    @20
    @43
    @24
    @25
    @41
    @1
    @5
    @41
    eqid
    #
    @26
    grpsubf
    3syl
    @0
    @39
    cB
    @42
    @41
    @5
    @0
    cB
    @41
    @0
    cB
    @33
    cc0
    cfsupp
    wbr
    vh
    cr
    cI
    cmap
    co
    #
    crab
    #
    @41
    cB
    vh
    cH
    cI
    cV
    rrxval.r
    rrxbase.b
    rrxbase
    @21
    @0
    @46
    @41
    wceq
    @22
    @46
    crefld
    vh
    @1
    cI
    cr
    crg
    cV
    cc0
    @23
    rebase
    re0g
    @46
    eqid
    frlmbas
    mpan
    eqtrd
    #
    sqxpeqd
    @47
    feq23d
    mpbird
    #
    fovrnda
    @0
    @5
    @39
    wfn
    #
    @5
    vf
    vg
    cB
    cB
    @27
    cmpt2
    wceq
    @0
    @40
    @49
    @48
    @39
    cB
    @5
    ffn
    syl
    vf
    vg
    cB
    cB
    @5
    fnov
    sylib
    @0
    vh
    cB
    @38
    cmpt
    cH
    cnm
    cfv
    @4
    vx
    cB
    vh
    cH
    cI
    cV
    rrxval.r
    rrxbase.b
    rrxnm
    @0
    cH
    @2
    cnm
    @18
    fveq2d
    eqtr2d
    @33
    @27
    wceq
    #
    @37
    @31
    csqrt
    @50
    @36
    @30
    crefld
    cgsu
    @50
    vx
    cI
    @35
    @29
    @50
    @34
    @28
    c2
    cexp
    @7
    @33
    @27
    fveq1
    oveq1d
    mpteq2dv
    oveq2d
    fveq2d
    fmpt2co
    @0
    vf
    vg
    cB
    cB
    @32
    @16
    @0
    @8
    cB
    wcel
    #
    @10
    cB
    wcel
    #
    w3a
    #
    @31
    @15
    csqrt
    @53
    @30
    @14
    crefld
    cgsu
    @53
    vx
    cI
    @29
    @13
    @53
    @7
    cI
    wcel
    wa
    #
    @28
    @12
    c2
    cexp
    @53
    vx
    cI
    @12
    @27
    cr
    @53
    @8
    @10
    crefld
    csg
    cfv
    #
    cof
    co
    #
    vx
    cI
    @9
    @11
    @55
    co
    #
    cmpt
    @27
    vx
    cI
    @12
    cmpt
    @53
    vx
    cI
    cI
    @9
    @11
    @55
    cI
    @8
    @10
    cV
    cV
    @53
    cI
    cr
    @8
    wf
    #
    @8
    cI
    wfn
    @53
    @8
    @45
    wcel
    #
    @58
    @53
    @0
    @8
    @41
    wcel
    #
    @59
    @0
    @51
    @52
    simp1
    #
    @0
    @51
    @52
    @60
    @0
    @51
    @52
    wa
    #
    wa
    #
    @8
    cB
    @41
    @0
    @51
    @52
    simprl
    @0
    cB
    @41
    wceq
    @62
    @47
    adantr
    #
    eleqtrd
    #
    3impb
    @41
    crefld
    @1
    cI
    cr
    cV
    @8
    @23
    rebase
    @44
    frlmbasmap
    syl2anc
    @8
    cr
    cI
    elmapi
    syl
    #
    cI
    cr
    @8
    ffn
    syl
    @53
    cI
    cr
    @10
    wf
    #
    @10
    cI
    wfn
    @53
    @10
    @45
    wcel
    #
    @67
    @53
    @0
    @10
    @41
    wcel
    #
    @68
    @61
    @0
    @51
    @52
    @69
    @63
    @10
    cB
    @41
    @0
    @51
    @52
    simprr
    @64
    eleqtrd
    #
    3impb
    @41
    crefld
    @1
    cI
    cr
    cV
    @10
    @23
    rebase
    @44
    frlmbasmap
    syl2anc
    @10
    cr
    cI
    elmapi
    syl
    #
    cI
    cr
    @10
    ffn
    syl
    @61
    @61
    cI
    inidm
    @54
    @9
    eqidd
    @54
    @11
    eqidd
    offval
    @0
    @51
    @52
    @27
    @56
    wceq
    @63
    @41
    crefld
    @8
    @10
    cI
    @5
    @55
    cV
    @1
    @23
    @44
    @21
    @63
    @22
    a1i
    @0
    @62
    simpl
    @65
    @70
    @55
    eqid
    #
    @26
    frlmsubgval
    3impb
    @53
    vx
    cI
    @12
    @57
    @54
    @9
    cr
    wcel
    @11
    cr
    wcel
    @12
    @57
    wceq
    @53
    cI
    cr
    @7
    @8
    @66
    ffvelrnda
    #
    @53
    cI
    cr
    @7
    @10
    @71
    ffvelrnda
    #
    @55
    @9
    @11
    @72
    resubgval
    syl2anc
    mpteq2dva
    3eqtr4d
    @54
    @9
    @11
    @73
    @74
    resubcld
    fvmpt2d
    oveq1d
    mpteq2dva
    oveq2d
    fveq2d
    mpt2eq3dva
    eqtrd
    3eqtr2rd
end
