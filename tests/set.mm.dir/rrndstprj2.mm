include "cfn.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "w3a.mm"
include "crp.mm"
include "cv.mm"
include "cfv.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "wral.mm"
include "wa.mm"
include "crrn.mm"
include "cmin.mm"
include "c2.mm"
include "cexp.mm"
include "csu.mm"
include "csqrt.mm"
include "chash.mm"
include "cmul.mm"
include "wceq.mm"
include "simpl1.mm"
include "eldifad.mm"
include "simpl2.mm"
include "simpl3.mm"
include "rrnmval.mm"
include "syl3anc.mm"
include "wne.mm"
include "eldifsni.mm"
include "syl.mm"
include "cr.mm"
include "cmap.mm"
include "wf.mm"
include "syl6eleq.mm"
include "elmapi.mm"
include "ffvelrnda.mm"
include "resubcld.mm"
include "resqcld.mm"
include "simprl.mm"
include "rpred.mm"
include "adantr.mm"
include "cabs.mm"
include "absresq.mm"
include "remetdval.mm"
include "syl2anc.mm"
include "simprr.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "breq1d.mm"
include "rspccva.mm"
include "sylan.mm"
include "eqbrtrrd.mm"
include "recnd.mm"
include "abscld.mm"
include "absge0d.mm"
include "cc0.mm"
include "cle.mm"
include "rpge0d.mm"
include "lt2sqd.mm"
include "mpbid.mm"
include "fsumlt.mm"
include "fsumrecl.mm"
include "sqge0d.mm"
include "fsumge0.mm"
include "resqrtth.mm"
include "cn.mm"
include "wb.mm"
include "hashnncl.mm"
include "mpbird.mm"
include "nnrpd.mm"
include "oveq2d.mm"
include "rpcnd.mm"
include "mulcomd.mm"
include "eqtrd.mm"
include "rpsqrtcld.mm"
include "sqmuld.mm"
include "cc.mm"
include "fsumconst.mm"
include "3eqtr4d.mm"
include "3brtr4d.mm"
include "resqrtcld.mm"
include "rpmulcld.mm"
include "sqrtge0d.mm"
include "eqbrtrd.mm"

theorem rrndstprj2
  let cR: class R
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cI: class I
  let cM: class M
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  let vi: setvar i
  let vj: setvar j
  let vm: setvar m
  let vz: setvar z
  let wph: wff ph
  let cA: class A
  let cJ: class J
  let cP: class P
  let vt: setvar t
  assume rrnval.1: |- X = ( RR ^m I )
  assume rrndstprj1.1: |- M = ( ( abs o. - ) |` ( RR X. RR ) )

  disjoint G n
  disjoint I n
  disjoint M n
  disjoint R n
  disjoint F n
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint G k
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint G x
  disjoint G y
  disjoint i j
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint I i
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint I j
  disjoint k m
  disjoint k z
  disjoint I k
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint I m
  disjoint n z
  disjoint x z
  disjoint I x
  disjoint y z
  disjoint I y
  disjoint I z
  disjoint M j
  disjoint M k
  disjoint j ph
  disjoint k ph
  disjoint n ph
  disjoint ph x
  disjoint A k
  disjoint J x
  disjoint P j
  disjoint P k
  disjoint P n
  disjoint P x
  disjoint P y
  disjoint R k
  disjoint X i
  disjoint X j
  disjoint X k
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint j t
  disjoint F j
  disjoint k t
  disjoint F k
  disjoint m t
  disjoint F m
  disjoint n t
  disjoint t x
  disjoint t y
  disjoint F t
  disjoint F x
  disjoint F y
  assert |- ( ( ( I e. ( Fin \ { (/) } ) /\ F e. X /\ G e. X ) /\ ( R e. RR+ /\ A. n e. I ( ( F ` n ) M ( G ` n ) ) < R ) ) -> ( F ( Rn ` I ) G ) < ( R x. ( sqrt ` ( # ` I ) ) ) )

  proof
    cI
    cfn
    c0
    csn
    #
    cdif
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
    cR
    crp
    wcel
    #
    vn
    cv
    #
    cF
    cfv
    #
    @6
    cG
    cfv
    #
    cM
    co
    #
    cR
    clt
    wbr
    #
    vn
    cI
    wral
    #
    wa
    #
    wa
    #
    cF
    cG
    cI
    crrn
    cfv
    co
    #
    cI
    vk
    cv
    #
    cF
    cfv
    #
    @15
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
    #
    cR
    cI
    chash
    cfv
    #
    csqrt
    cfv
    #
    cmul
    co
    #
    clt
    @13
    cI
    cfn
    wcel
    #
    @2
    @3
    @14
    @21
    wceq
    @13
    cI
    cfn
    @0
    @1
    @2
    @3
    @12
    simpl1
    #
    eldifad
    #
    @1
    @2
    @3
    @12
    simpl2
    #
    @1
    @2
    @3
    @12
    simpl3
    #
    vk
    cF
    cG
    cI
    cX
    rrnval.1
    rrnmval
    syl3anc
    @13
    @21
    @24
    clt
    wbr
    @21
    c2
    cexp
    co
    #
    @24
    c2
    cexp
    co
    #
    clt
    wbr
    @13
    @20
    cI
    cR
    c2
    cexp
    co
    #
    vk
    csu
    #
    @30
    @31
    clt
    @13
    cI
    @19
    @32
    vk
    @27
    @13
    @1
    cI
    c0
    wne
    #
    @26
    cI
    cfn
    c0
    eldifsni
    syl
    #
    @13
    @15
    cI
    wcel
    #
    wa
    #
    @18
    @37
    @16
    @17
    @13
    cI
    cr
    @15
    cF
    @13
    cF
    cr
    cI
    cmap
    co
    #
    wcel
    cI
    cr
    cF
    wf
    @13
    cF
    cX
    @38
    @28
    rrnval.1
    syl6eleq
    cF
    cr
    cI
    elmapi
    syl
    ffvelrnda
    #
    @13
    cI
    cr
    @15
    cG
    @13
    cG
    @38
    wcel
    cI
    cr
    cG
    wf
    @13
    cG
    cX
    @38
    @29
    rrnval.1
    syl6eleq
    cG
    cr
    cI
    elmapi
    syl
    ffvelrnda
    #
    resubcld
    #
    resqcld
    #
    @13
    @32
    cr
    wcel
    @36
    @13
    cR
    @13
    cR
    @4
    @5
    @11
    simprl
    #
    rpred
    #
    resqcld
    #
    adantr
    @37
    @18
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    @19
    @32
    clt
    @37
    @18
    cr
    wcel
    @47
    @19
    wceq
    @41
    @18
    absresq
    syl
    @37
    @46
    cR
    clt
    wbr
    @47
    @32
    clt
    wbr
    @37
    @16
    @17
    cM
    co
    #
    @46
    cR
    clt
    @37
    @16
    cr
    wcel
    @17
    cr
    wcel
    @48
    @46
    wceq
    @39
    @40
    @16
    @17
    cM
    rrndstprj1.1
    remetdval
    syl2anc
    @13
    @11
    @36
    @48
    cR
    clt
    wbr
    #
    @4
    @5
    @11
    simprr
    @10
    @49
    vn
    @15
    cI
    @6
    @15
    wceq
    #
    @9
    @48
    cR
    clt
    @50
    @7
    @16
    @8
    @17
    cM
    @6
    @15
    cF
    fveq2
    @6
    @15
    cG
    fveq2
    oveq12d
    breq1d
    rspccva
    sylan
    eqbrtrrd
    @37
    @46
    cR
    @37
    @18
    @37
    @18
    @41
    recnd
    #
    abscld
    @13
    cR
    cr
    wcel
    @36
    @44
    adantr
    @37
    @18
    @51
    absge0d
    @13
    cc0
    cR
    cle
    wbr
    @36
    @13
    cR
    @43
    rpge0d
    adantr
    lt2sqd
    mpbid
    eqbrtrrd
    fsumlt
    @13
    @20
    cr
    wcel
    cc0
    @20
    cle
    wbr
    @30
    @20
    wceq
    @13
    cI
    @19
    vk
    @27
    @42
    fsumrecl
    #
    @13
    cI
    @19
    vk
    @27
    @42
    @37
    @18
    @41
    sqge0d
    fsumge0
    #
    @20
    resqrtth
    syl2anc
    @13
    @32
    @23
    c2
    cexp
    co
    #
    cmul
    co
    #
    @22
    @32
    cmul
    co
    #
    @31
    @33
    @13
    @55
    @32
    @22
    cmul
    co
    @56
    @13
    @54
    @22
    @32
    cmul
    @13
    @22
    cr
    wcel
    cc0
    @22
    cle
    wbr
    @54
    @22
    wceq
    @13
    @22
    @13
    @22
    @13
    @22
    cn
    wcel
    #
    @34
    @35
    @13
    @25
    @57
    @34
    wb
    @27
    cI
    hashnncl
    syl
    mpbird
    nnrpd
    #
    rpred
    @13
    @22
    @58
    rpge0d
    @22
    resqrtth
    syl2anc
    oveq2d
    @13
    @32
    @22
    @13
    @32
    @45
    recnd
    #
    @13
    @22
    @58
    rpcnd
    mulcomd
    eqtrd
    @13
    cR
    @23
    @13
    cR
    @43
    rpcnd
    @13
    @23
    @13
    @22
    @58
    rpsqrtcld
    #
    rpcnd
    sqmuld
    @13
    @25
    @32
    cc
    wcel
    @33
    @56
    wceq
    @27
    @59
    cI
    @32
    vk
    fsumconst
    syl2anc
    3eqtr4d
    3brtr4d
    @13
    @21
    @24
    @13
    @20
    @52
    @53
    resqrtcld
    @13
    @24
    @13
    cR
    @23
    @43
    @60
    rpmulcld
    #
    rpred
    @13
    @20
    @52
    @53
    sqrtge0d
    @13
    @24
    @61
    rpge0d
    lt2sqd
    mpbird
    eqbrtrd
end
