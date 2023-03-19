include "co.mm"
include "csqrt.mm"
include "cfv.mm"
include "cmul.mm"
include "clt.mm"
include "wbr.mm"
include "cv.mm"
include "cmin.mm"
include "c2.mm"
include "cexp.mm"
include "csu.mm"
include "cabs.mm"
include "wcel.mm"
include "wa.mm"
include "cc.mm"
include "cr.mm"
include "cmap.mm"
include "wf.mm"
include "elmapi.mm"
include "syl.mm"
include "wss.mm"
include "ax-resscn.mm"
include "a1i.mm"
include "fssd.mm"
include "ffvelrnda.mm"
include "subcld.mm"
include "abscld.mm"
include "resqcld.mm"
include "rpred.mm"
include "adantr.mm"
include "cc0.mm"
include "cle.mm"
include "wb.mm"
include "absge0d.mm"
include "crp.mm"
include "rpge0d.mm"
include "lt2sq.mm"
include "syl22anc.mm"
include "mpbid.mm"
include "fsumlt.mm"
include "wceq.mm"
include "resubcld.mm"
include "absresq.mm"
include "eqcomd.mm"
include "sumeq2dv.mm"
include "chash.mm"
include "cfn.mm"
include "sseldi.mm"
include "fsumconst.mm"
include "syl2anc.mm"
include "eqcom.mm"
include "mpbi.mm"
include "oveq1i.mm"
include "eqtr2d.mm"
include "breq12d.mm"
include "mpbird.mm"
include "nfv.mm"
include "fsumreclf.mm"
include "sqge0d.mm"
include "fsumge0.mm"
include "cn0.mm"
include "hashcl.mm"
include "syl5eqel.mm"
include "nn0red.mm"
include "remulcld.mm"
include "nn0ge0d.mm"
include "mulge0d.mm"
include "sqrtltd.mm"
include "crrx.mm"
include "cds.mm"
include "cmpt2.mm"
include "eqid.mm"
include "rrxdsfi.mm"
include "eqtrd.mm"
include "fveq1.mm"
include "adantl.mm"
include "oveq12d.mm"
include "oveq1d.mm"
include "sumeq2ad.mm"
include "fveq2d.mm"
include "resqrtcld.mm"
include "ovmpt2d.mm"
include "sqrtmul.mm"
include "sqrtsqd.mm"
include "oveq2d.mm"

theorem rrndistlt
  let wph: wff ph
  let cD: class D
  let vi: setvar i
  let cE: class E
  let cI: class I
  let cN: class N
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let vx: setvar x
  assume rrndistlt.i: |- ( ph -> I e. Fin )
  assume rrndistlt.z: |- ( ph -> I =/= (/) )
  assume rrndistlt.n: |- N = ( # ` I )
  assume rrndistlt.x: |- ( ph -> X e. ( RR ^m I ) )
  assume rrndistlt.y: |- ( ph -> Y e. ( RR ^m I ) )
  assume rrndistlt.l: |- ( ( ph /\ i e. I ) -> ( abs ` ( ( X ` i ) - ( Y ` i ) ) ) < E )
  assume rrndistlt.e: |- ( ph -> E e. RR+ )
  assume rrndistlt.d: |- D = ( dist ` ( RR^ ` I ) )

  disjoint E i
  disjoint I i
  disjoint X i
  disjoint Y i
  disjoint i ph
  disjoint I f
  disjoint I g
  disjoint f g
  disjoint f i
  disjoint g i
  disjoint X f
  disjoint X g
  disjoint Y f
  disjoint Y g
  disjoint f ph
  disjoint g ph
  disjoint k x
  assert |- ( ph -> ( X D Y ) < ( ( sqrt ` N ) x. E ) )

  proof
    wph
    cX
    cY
    cD
    co
    #
    cN
    csqrt
    cfv
    #
    cE
    cmul
    co
    #
    clt
    wbr
    cI
    vi
    cv
    #
    cX
    cfv
    #
    @3
    cY
    cfv
    #
    cmin
    co
    #
    c2
    cexp
    co
    #
    vi
    csu
    #
    csqrt
    cfv
    #
    cN
    cE
    c2
    cexp
    co
    #
    cmul
    co
    #
    csqrt
    cfv
    #
    clt
    wbr
    #
    wph
    @8
    @11
    clt
    wbr
    #
    @13
    wph
    @14
    cI
    @6
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    vi
    csu
    #
    cI
    @10
    vi
    csu
    #
    clt
    wbr
    wph
    cI
    @16
    @10
    vi
    rrndistlt.i
    rrndistlt.z
    wph
    @3
    cI
    wcel
    #
    wa
    #
    @15
    @20
    @6
    @20
    @4
    @5
    wph
    cI
    cc
    @3
    cX
    wph
    cI
    cr
    cc
    cX
    wph
    cX
    cr
    cI
    cmap
    co
    #
    wcel
    cI
    cr
    cX
    wf
    rrndistlt.x
    cX
    cr
    cI
    elmapi
    syl
    #
    cr
    cc
    wss
    wph
    ax-resscn
    a1i
    #
    fssd
    ffvelrnda
    wph
    cI
    cc
    @3
    cY
    wph
    cI
    cr
    cc
    cY
    wph
    cY
    @21
    wcel
    cI
    cr
    cY
    wf
    rrndistlt.y
    cY
    cr
    cI
    elmapi
    syl
    #
    @23
    fssd
    ffvelrnda
    subcld
    #
    abscld
    #
    resqcld
    wph
    @10
    cr
    wcel
    #
    @19
    wph
    cE
    wph
    cE
    rrndistlt.e
    rpred
    #
    resqcld
    #
    adantr
    @20
    @15
    cE
    clt
    wbr
    #
    @16
    @10
    clt
    wbr
    #
    rrndistlt.l
    @20
    @15
    cr
    wcel
    cc0
    @15
    cle
    wbr
    cE
    cr
    wcel
    #
    cc0
    cE
    cle
    wbr
    @30
    @31
    wb
    @26
    @20
    @6
    @25
    absge0d
    wph
    @32
    @19
    @28
    adantr
    @20
    cE
    wph
    cE
    crp
    wcel
    @19
    rrndistlt.e
    adantr
    rpge0d
    @15
    cE
    lt2sq
    syl22anc
    mpbid
    fsumlt
    wph
    @8
    @17
    @11
    @18
    clt
    wph
    cI
    @7
    @16
    vi
    @20
    @16
    @7
    @20
    @6
    cr
    wcel
    @16
    @7
    wceq
    @20
    @4
    @5
    wph
    cI
    cr
    @3
    cX
    @22
    ffvelrnda
    wph
    cI
    cr
    @3
    cY
    @24
    ffvelrnda
    resubcld
    #
    @6
    absresq
    syl
    eqcomd
    sumeq2dv
    wph
    @18
    cI
    chash
    cfv
    #
    @10
    cmul
    co
    #
    @11
    wph
    cI
    cfn
    wcel
    #
    @10
    cc
    wcel
    @18
    @35
    wceq
    rrndistlt.i
    wph
    cr
    cc
    @10
    ax-resscn
    @29
    sseldi
    cI
    @10
    vi
    fsumconst
    syl2anc
    @35
    @11
    wceq
    wph
    @34
    cN
    @10
    cmul
    cN
    @34
    wceq
    @34
    cN
    wceq
    rrndistlt.n
    cN
    @34
    eqcom
    mpbi
    oveq1i
    a1i
    eqtr2d
    breq12d
    mpbird
    wph
    @8
    @11
    wph
    cI
    @7
    vi
    wph
    vi
    nfv
    rrndistlt.i
    @20
    @6
    @33
    resqcld
    #
    fsumreclf
    #
    wph
    cI
    @7
    vi
    rrndistlt.i
    @37
    @20
    @6
    @33
    sqge0d
    fsumge0
    #
    wph
    cN
    @10
    wph
    cN
    wph
    cN
    @34
    cn0
    rrndistlt.n
    wph
    @36
    @34
    cn0
    wcel
    rrndistlt.i
    cI
    hashcl
    syl
    syl5eqel
    #
    nn0red
    #
    @29
    remulcld
    wph
    cN
    @10
    @41
    @29
    wph
    cN
    @40
    nn0ge0d
    #
    wph
    cE
    @28
    sqge0d
    #
    mulge0d
    sqrtltd
    mpbid
    wph
    @0
    @9
    @2
    @12
    clt
    wph
    vf
    vg
    cX
    cY
    @21
    @21
    cI
    @3
    vf
    cv
    #
    cfv
    #
    @3
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
    vi
    csu
    #
    csqrt
    cfv
    #
    @9
    cD
    cr
    wph
    cD
    cI
    crrx
    cfv
    #
    cds
    cfv
    #
    vf
    vg
    @21
    @21
    @51
    cmpt2
    #
    cD
    @53
    wceq
    wph
    rrndistlt.d
    a1i
    wph
    @36
    @53
    @54
    wceq
    rrndistlt.i
    @21
    vf
    vg
    vi
    @52
    cI
    @52
    eqid
    @21
    eqid
    rrxdsfi
    syl
    eqtrd
    @44
    cX
    wceq
    #
    @46
    cY
    wceq
    #
    wa
    #
    @51
    @9
    wceq
    wph
    @57
    @50
    @8
    csqrt
    @57
    cI
    @49
    @7
    vi
    @57
    @48
    @6
    c2
    cexp
    @57
    @45
    @4
    @47
    @5
    cmin
    @55
    @45
    @4
    wceq
    @56
    @3
    @44
    cX
    fveq1
    adantr
    @56
    @47
    @5
    wceq
    @55
    @3
    @46
    cY
    fveq1
    adantl
    oveq12d
    oveq1d
    sumeq2ad
    fveq2d
    adantl
    rrndistlt.x
    rrndistlt.y
    wph
    @8
    @38
    @39
    resqrtcld
    ovmpt2d
    wph
    @12
    @1
    @10
    csqrt
    cfv
    #
    cmul
    co
    #
    @2
    wph
    cN
    cr
    wcel
    cc0
    cN
    cle
    wbr
    @27
    cc0
    @10
    cle
    wbr
    @12
    @59
    wceq
    @41
    @42
    @29
    @43
    cN
    @10
    sqrtmul
    syl22anc
    wph
    @58
    cE
    @1
    cmul
    wph
    cE
    @28
    wph
    cE
    rrndistlt.e
    rpge0d
    sqrtsqd
    oveq2d
    eqtr2d
    breq12d
    mpbird
end
