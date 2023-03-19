include "wcel.mm"
include "w3a.mm"
include "crefld.mm"
include "cv.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "c2.mm"
include "cexp.mm"
include "cmpt.mm"
include "cgsu.mm"
include "csqrt.mm"
include "cc0.mm"
include "csupp.mm"
include "cun.mm"
include "csu.mm"
include "cvv.mm"
include "cmpt2.mm"
include "wceq.mm"
include "crrx.mm"
include "cbs.mm"
include "cds.mm"
include "eqid.mm"
include "rrxds.mm"
include "syl6reqr.mm"
include "cfsupp.mm"
include "wbr.mm"
include "cr.mm"
include "cmap.mm"
include "crab.mm"
include "rrxbase.mm"
include "mpt2eq12.mm"
include "syl2anc.mm"
include "eqtr4d.mm"
include "3ad2ant1.mm"
include "wa.mm"
include "simprl.mm"
include "fveq1d.mm"
include "simprr.mm"
include "oveq12d.mm"
include "oveq1d.mm"
include "mpteq2dv.mm"
include "oveq2d.mm"
include "wf.mm"
include "simp2.mm"
include "rrxf.mm"
include "ffvelrnda.mm"
include "simp3.mm"
include "resubcld.mm"
include "resqcld.mm"
include "fmptd.mm"
include "cfn.mm"
include "wss.mm"
include "rrxfsupp.mm"
include "unfi.mm"
include "rrxmvallem.mm"
include "ssfi.mm"
include "wb.mm"
include "mptexg.mm"
include "wfun.mm"
include "cc.mm"
include "funmpt.mm"
include "0cn.mm"
include "funisfsupp.mm"
include "mp3an13.mm"
include "syl.mm"
include "mpbird.mm"
include "simp1.mm"
include "regsumsupp.mm"
include "syl3anc.mm"
include "cdm.mm"
include "suppssdm.mm"
include "dmmptss.mm"
include "sstri.mm"
include "a1i.mm"
include "sselda.mm"
include "eqidd.mm"
include "simpr.mm"
include "fveq2d.mm"
include "ovexd.mm"
include "fvmptd.mm"
include "eqcomd.mm"
include "syldan.mm"
include "sumeq2dv.mm"
include "adantr.mm"
include "recnd.mm"
include "subcld.mm"
include "sqcld.mm"
include "cdif.mm"
include "rrxsuppss.mm"
include "unssd.mm"
include "ssdifssd.mm"
include "ssdifd.mm"
include "ssid.mm"
include "0cnd.mm"
include "suppssr.mm"
include "eqtrd.mm"
include "fsumss.mm"
include "3eqtrd.mm"
include "fvexd.mm"
include "ovmpt2d.mm"

theorem rrxmval
  let cD: class D
  let vh: setvar h
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cI: class I
  let cV: class V
  let cX: class X
  let cA: class A
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume rrxmval.1: |- X = { h e. ( RR ^m I ) | h finSupp 0 }
  assume rrxmval.d: |- D = ( dist ` ( RR^ ` I ) )

  disjoint F h
  disjoint F k
  disjoint h k
  disjoint G h
  disjoint G k
  disjoint I h
  disjoint I k
  disjoint V h
  disjoint V k
  disjoint X k
  disjoint A k
  disjoint D f
  disjoint D g
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint f g
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint F f
  disjoint F g
  disjoint F x
  disjoint f h
  disjoint f k
  disjoint g h
  disjoint g k
  disjoint h x
  disjoint k x
  disjoint G f
  disjoint G g
  disjoint G x
  disjoint I f
  disjoint I g
  disjoint I x
  disjoint I y
  disjoint I z
  disjoint h y
  disjoint h z
  disjoint k y
  disjoint k z
  disjoint V f
  disjoint V g
  disjoint V x
  disjoint V y
  disjoint V z
  disjoint X f
  disjoint X g
  disjoint X x
  disjoint X y
  disjoint X z
  assert |- ( ( I e. V /\ F e. X /\ G e. X ) -> ( F D G ) = ( sqrt ` sum_ k e. ( ( F supp 0 ) u. ( G supp 0 ) ) ( ( ( F ` k ) - ( G ` k ) ) ^ 2 ) ) )

  proof
    cI
    cV
    wcel
    #
    cF
    cX
    wcel
    #
    cG
    cX
    wcel
    #
    w3a
    #
    vf
    vg
    cF
    cG
    cX
    cX
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
    @4
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
    cF
    cc0
    csupp
    co
    #
    cG
    cc0
    csupp
    co
    #
    cun
    #
    vk
    cv
    #
    cF
    cfv
    #
    @17
    cG
    cfv
    #
    cmin
    co
    #
    c2
    cexp
    co
    #
    vk
    csu
    #
    csqrt
    cfv
    cD
    cvv
    @0
    @1
    cD
    vf
    vg
    cX
    cX
    @13
    cmpt2
    #
    wceq
    @2
    @0
    cD
    vf
    vg
    cI
    crrx
    cfv
    #
    cbs
    cfv
    #
    @25
    @13
    cmpt2
    #
    @23
    @0
    @26
    @24
    cds
    cfv
    cD
    vx
    @25
    vf
    vg
    @24
    cI
    cV
    @24
    eqid
    #
    @25
    eqid
    #
    rrxds
    rrxmval.d
    syl6reqr
    @0
    cX
    @25
    wceq
    #
    @29
    @23
    @26
    wceq
    @0
    @25
    vh
    cv
    cc0
    cfsupp
    wbr
    vh
    cr
    cI
    cmap
    co
    crab
    cX
    @25
    vh
    @24
    cI
    cV
    @27
    @28
    rrxbase
    rrxmval.1
    syl6reqr
    #
    @30
    vf
    vg
    cX
    cX
    @25
    @25
    @13
    mpt2eq12
    syl2anc
    eqtr4d
    3ad2ant1
    @3
    @5
    cF
    wceq
    #
    @7
    cG
    wceq
    #
    wa
    #
    wa
    #
    @12
    @22
    csqrt
    @34
    @12
    crefld
    vx
    cI
    @4
    cF
    cfv
    #
    @4
    cG
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
    @39
    cc0
    csupp
    co
    #
    @21
    vk
    csu
    #
    @22
    @34
    @11
    @39
    crefld
    cgsu
    @34
    vx
    cI
    @10
    @38
    @34
    @9
    @37
    c2
    cexp
    @34
    @6
    @35
    @8
    @36
    cmin
    @34
    @4
    @5
    cF
    @3
    @31
    @32
    simprl
    fveq1d
    @34
    @4
    @7
    cG
    @3
    @31
    @32
    simprr
    fveq1d
    oveq12d
    oveq1d
    mpteq2dv
    oveq2d
    @3
    @40
    @42
    wceq
    @33
    @3
    @40
    @41
    @17
    @39
    cfv
    #
    vk
    csu
    #
    @42
    @3
    cI
    cr
    @39
    wf
    @39
    cc0
    cfsupp
    wbr
    #
    @0
    @40
    @44
    wceq
    @3
    vx
    cI
    @38
    cr
    @39
    @3
    @4
    cI
    wcel
    wa
    #
    @37
    @46
    @35
    @36
    @3
    cI
    cr
    @4
    cF
    @3
    vh
    cF
    cI
    cX
    rrxmval.1
    @0
    @1
    @2
    simp2
    #
    rrxf
    #
    ffvelrnda
    @3
    cI
    cr
    @4
    cG
    @3
    vh
    cG
    cI
    cX
    rrxmval.1
    @0
    @1
    @2
    simp3
    #
    rrxf
    #
    ffvelrnda
    resubcld
    resqcld
    @39
    eqid
    #
    fmptd
    #
    @3
    @45
    @41
    cfn
    wcel
    #
    @3
    @16
    cfn
    wcel
    #
    @41
    @16
    wss
    @53
    @3
    @14
    cfn
    wcel
    @15
    cfn
    wcel
    @54
    @3
    vh
    cF
    cI
    cX
    rrxmval.1
    @47
    rrxfsupp
    @3
    vh
    cG
    cI
    cX
    rrxmval.1
    @49
    rrxfsupp
    @14
    @15
    unfi
    syl2anc
    #
    vh
    vx
    cF
    cG
    cI
    cV
    cX
    rrxmval.1
    rrxmvallem
    #
    @16
    @41
    ssfi
    syl2anc
    @0
    @1
    @45
    @53
    wb
    #
    @2
    @0
    @39
    cvv
    wcel
    #
    @57
    vx
    cI
    @38
    cV
    mptexg
    @39
    wfun
    @58
    cc0
    cc
    wcel
    @57
    vx
    cI
    @38
    funmpt
    0cn
    @39
    cvv
    cc
    cc0
    funisfsupp
    mp3an13
    syl
    3ad2ant1
    mpbird
    @0
    @1
    @2
    simp1
    #
    vk
    @39
    cI
    cV
    regsumsupp
    syl3anc
    @3
    @41
    @21
    @43
    vk
    @3
    @17
    @41
    wcel
    #
    @17
    cI
    wcel
    #
    @21
    @43
    wceq
    #
    @3
    @41
    cI
    @17
    @41
    cI
    wss
    @3
    @41
    @39
    cdm
    cI
    @39
    cc0
    suppssdm
    vx
    cI
    @38
    @39
    @51
    dmmptss
    sstri
    a1i
    sselda
    #
    @3
    @61
    wa
    #
    @43
    @21
    @64
    vx
    @17
    @38
    @21
    cI
    @39
    cvv
    @64
    @39
    eqidd
    @64
    @4
    @17
    wceq
    #
    wa
    #
    @37
    @20
    c2
    cexp
    @66
    @35
    @18
    @36
    @19
    cmin
    @66
    @4
    @17
    cF
    @64
    @65
    simpr
    #
    fveq2d
    @66
    @4
    @17
    cG
    @67
    fveq2d
    oveq12d
    oveq1d
    @3
    @61
    simpr
    @64
    @20
    c2
    cexp
    ovexd
    fvmptd
    eqcomd
    #
    syldan
    sumeq2dv
    eqtr4d
    adantr
    @3
    @42
    @22
    wceq
    @33
    @3
    @41
    @16
    @21
    vk
    @56
    @3
    @60
    @61
    @21
    cc
    wcel
    @63
    @64
    @20
    @64
    @18
    @19
    @64
    @18
    @3
    cI
    cr
    @17
    cF
    @48
    ffvelrnda
    recnd
    @64
    @19
    @3
    cI
    cr
    @17
    cG
    @50
    ffvelrnda
    recnd
    subcld
    sqcld
    syldan
    @3
    @17
    @16
    @41
    cdif
    #
    wcel
    #
    wa
    @21
    @43
    cc0
    @3
    @70
    @61
    @62
    @3
    @69
    cI
    @17
    @3
    @16
    cI
    @41
    @3
    @14
    @15
    cI
    @3
    vh
    cF
    cI
    cX
    rrxmval.1
    @47
    rrxsuppss
    @3
    vh
    cG
    cI
    cX
    rrxmval.1
    @49
    rrxsuppss
    unssd
    #
    ssdifssd
    sselda
    @68
    syldan
    @3
    @70
    @17
    cI
    @41
    cdif
    #
    wcel
    @43
    cc0
    wceq
    @3
    @69
    @72
    @17
    @3
    @16
    cI
    @41
    @71
    ssdifd
    sselda
    @3
    cI
    cr
    cc
    @39
    cV
    @41
    @17
    cc0
    @52
    @41
    @41
    wss
    @3
    @41
    ssid
    a1i
    @59
    @3
    0cnd
    suppssr
    syldan
    eqtrd
    @55
    fsumss
    adantr
    3eqtrd
    fveq2d
    @47
    @49
    @3
    @22
    csqrt
    fvexd
    ovmpt2d
end
