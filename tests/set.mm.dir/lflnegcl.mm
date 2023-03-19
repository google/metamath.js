include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "wf.mm"
include "cv.mm"
include "cvsca.mm"
include "co.mm"
include "cplusg.mm"
include "cmulr.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "cgrp.mm"
include "crg.mm"
include "clmod.mm"
include "lmodring.mm"
include "syl.mm"
include "ringgrp.mm"
include "adantr.mm"
include "simpr.mm"
include "eqid.mm"
include "lflcl.mm"
include "syl3anc.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "fmptd.mm"
include "w3a.mm"
include "cabl.mm"
include "ringabl.mm"
include "simpr1.mm"
include "simpr2.mm"
include "ringcl.mm"
include "simpr3.mm"
include "ablinvadd.mm"
include "lfli.mm"
include "syl113anc.mm"
include "fveq2d.mm"
include "ringmneg2.mm"
include "oveq1d.mm"
include "3eqtr4d.mm"
include "lmodvscl.mm"
include "lmodvacl.mm"
include "fveq2.mm"
include "fvex.mm"
include "fvmpt.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "ralrimivvva.mm"
include "wb.mm"
include "islfl.mm"
include "mpbir2and.mm"

theorem lflnegcl
  let wph: wff ph
  let vx: setvar x
  let cR: class R
  let cF: class F
  let cG: class G
  let cI: class I
  let cN: class N
  let cV: class V
  let cW: class W
  let vy: setvar y
  let vk: setvar k
  let vz: setvar z
  let c.0: class .0.
  let c.pl: class .+
  assume lflnegcl.v: |- V = ( Base ` W )
  assume lflnegcl.r: |- R = ( Scalar ` W )
  assume lflnegcl.i: |- I = ( invg ` R )
  assume lflnegcl.n: |- N = ( x e. V |-> ( I ` ( G ` x ) ) )
  assume lflnegcl.f: |- F = ( LFnl ` W )
  assume lflnegcl.w: |- ( ph -> W e. LMod )
  assume lflnegcl.g: |- ( ph -> G e. F )

  disjoint G x
  disjoint I x
  disjoint R x
  disjoint V x
  disjoint W x
  disjoint ph x
  disjoint x y
  disjoint G y
  disjoint I y
  disjoint k y
  disjoint k z
  disjoint N k
  disjoint y z
  disjoint N y
  disjoint N z
  disjoint .0. y
  disjoint .+ y
  disjoint k x
  disjoint R k
  disjoint x z
  disjoint R y
  disjoint R z
  disjoint V y
  disjoint V z
  disjoint W k
  disjoint W y
  disjoint W z
  disjoint k ph
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> N e. F )

  proof
    wph
    cN
    cF
    wcel
    #
    cV
    cR
    cbs
    cfv
    #
    cN
    wf
    #
    vk
    cv
    #
    vy
    cv
    #
    cW
    cvsca
    cfv
    #
    co
    #
    vz
    cv
    #
    cW
    cplusg
    cfv
    #
    co
    #
    cN
    cfv
    #
    @3
    @4
    cN
    cfv
    #
    cR
    cmulr
    cfv
    #
    co
    #
    @7
    cN
    cfv
    #
    cR
    cplusg
    cfv
    #
    co
    #
    wceq
    #
    vz
    cV
    wral
    vy
    cV
    wral
    vk
    @1
    wral
    #
    wph
    vx
    cV
    vx
    cv
    #
    cG
    cfv
    #
    cI
    cfv
    #
    @1
    cN
    wph
    @19
    cV
    wcel
    #
    wa
    #
    cR
    cgrp
    wcel
    #
    @20
    @1
    wcel
    #
    @21
    @1
    wcel
    wph
    @24
    @22
    wph
    cR
    crg
    wcel
    #
    @24
    wph
    cW
    clmod
    wcel
    #
    @26
    lflnegcl.w
    cR
    cW
    lflnegcl.r
    lmodring
    syl
    #
    cR
    ringgrp
    syl
    adantr
    @23
    @27
    cG
    cF
    wcel
    #
    @22
    @25
    wph
    @27
    @22
    lflnegcl.w
    adantr
    wph
    @29
    @22
    lflnegcl.g
    adantr
    wph
    @22
    simpr
    cR
    cF
    cG
    @1
    cV
    cW
    @19
    clmod
    lflnegcl.r
    @1
    eqid
    #
    lflnegcl.v
    lflnegcl.f
    lflcl
    syl3anc
    @1
    cR
    cI
    @20
    @30
    lflnegcl.i
    grpinvcl
    syl2anc
    lflnegcl.n
    fmptd
    wph
    @17
    vk
    vy
    vz
    @1
    cV
    cV
    wph
    @3
    @1
    wcel
    #
    @4
    cV
    wcel
    #
    @7
    cV
    wcel
    #
    w3a
    #
    wa
    #
    @9
    cG
    cfv
    #
    cI
    cfv
    #
    @3
    @4
    cG
    cfv
    #
    cI
    cfv
    #
    @12
    co
    #
    @7
    cG
    cfv
    #
    cI
    cfv
    #
    @15
    co
    #
    @10
    @16
    @35
    @3
    @38
    @12
    co
    #
    @41
    @15
    co
    #
    cI
    cfv
    #
    @44
    cI
    cfv
    #
    @42
    @15
    co
    #
    @37
    @43
    @35
    cR
    cabl
    wcel
    #
    @44
    @1
    wcel
    #
    @41
    @1
    wcel
    #
    @46
    @48
    wceq
    wph
    @49
    @34
    wph
    @26
    @49
    @28
    cR
    ringabl
    syl
    adantr
    @35
    @26
    @31
    @38
    @1
    wcel
    #
    @50
    wph
    @26
    @34
    @28
    adantr
    #
    wph
    @31
    @32
    @33
    simpr1
    #
    @35
    @27
    @29
    @32
    @52
    wph
    @27
    @34
    lflnegcl.w
    adantr
    #
    wph
    @29
    @34
    lflnegcl.g
    adantr
    #
    wph
    @31
    @32
    @33
    simpr2
    #
    cR
    cF
    cG
    @1
    cV
    cW
    @4
    clmod
    lflnegcl.r
    @30
    lflnegcl.v
    lflnegcl.f
    lflcl
    syl3anc
    #
    @1
    cR
    @12
    @3
    @38
    @30
    @12
    eqid
    #
    ringcl
    syl3anc
    @35
    @27
    @29
    @33
    @51
    @55
    @56
    wph
    @31
    @32
    @33
    simpr3
    #
    cR
    cF
    cG
    @1
    cV
    cW
    @7
    clmod
    lflnegcl.r
    @30
    lflnegcl.v
    lflnegcl.f
    lflcl
    syl3anc
    @1
    @15
    cR
    cI
    @44
    @41
    @30
    @15
    eqid
    #
    lflnegcl.i
    ablinvadd
    syl3anc
    @35
    @36
    @45
    cI
    @35
    @27
    @29
    @31
    @32
    @33
    @36
    @45
    wceq
    @55
    @56
    @54
    @57
    @60
    cR
    @8
    @15
    @3
    @5
    @12
    cF
    cG
    @1
    cV
    cW
    @4
    @7
    clmod
    lflnegcl.v
    @8
    eqid
    #
    lflnegcl.r
    @5
    eqid
    #
    @30
    @61
    @59
    lflnegcl.f
    lfli
    syl113anc
    fveq2d
    @35
    @40
    @47
    @42
    @15
    @35
    @1
    cR
    @12
    cI
    @3
    @38
    @30
    @59
    lflnegcl.i
    @53
    @54
    @58
    ringmneg2
    oveq1d
    3eqtr4d
    @35
    @9
    cV
    wcel
    #
    @10
    @37
    wceq
    @35
    @27
    @6
    cV
    wcel
    #
    @33
    @64
    @55
    @35
    @27
    @31
    @32
    @65
    @55
    @54
    @57
    @3
    @5
    cR
    @1
    cV
    cW
    @4
    lflnegcl.v
    lflnegcl.r
    @63
    @30
    lmodvscl
    syl3anc
    @60
    @8
    cV
    cW
    @6
    @7
    lflnegcl.v
    @62
    lmodvacl
    syl3anc
    vx
    @9
    @21
    @37
    cV
    cN
    @19
    @9
    wceq
    @20
    @36
    cI
    @19
    @9
    cG
    fveq2
    fveq2d
    lflnegcl.n
    @36
    cI
    fvex
    fvmpt
    syl
    @35
    @13
    @40
    @14
    @42
    @15
    @35
    @11
    @39
    @3
    @12
    @35
    @32
    @11
    @39
    wceq
    @57
    vx
    @4
    @21
    @39
    cV
    cN
    @19
    @4
    wceq
    @20
    @38
    cI
    @19
    @4
    cG
    fveq2
    fveq2d
    lflnegcl.n
    @38
    cI
    fvex
    fvmpt
    syl
    oveq2d
    @35
    @33
    @14
    @42
    wceq
    @60
    vx
    @7
    @21
    @42
    cV
    cN
    @19
    @7
    wceq
    @20
    @41
    cI
    @19
    @7
    cG
    fveq2
    fveq2d
    lflnegcl.n
    @41
    cI
    fvex
    fvmpt
    syl
    oveq12d
    3eqtr4d
    ralrimivvva
    wph
    @27
    @0
    @2
    @18
    wa
    wb
    lflnegcl.w
    vy
    vz
    cR
    @8
    @15
    @5
    @12
    cF
    cN
    @1
    cV
    cW
    clmod
    vk
    lflnegcl.v
    @62
    lflnegcl.r
    @63
    @30
    @61
    @59
    lflnegcl.f
    islfl
    syl
    mpbir2and
end
