include "cioo.mm"
include "ccom.mm"
include "crn.mm"
include "cuni.mm"
include "cr.mm"
include "wss.mm"
include "cv.mm"
include "covol.mm"
include "cfv.mm"
include "wcel.mm"
include "cin.mm"
include "cdif.mm"
include "caddc.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "cvol.mm"
include "cdm.mm"
include "cn.mm"
include "wf.mm"
include "cxr.mm"
include "cxp.mm"
include "ioof.mm"
include "inss2.mm"
include "rexpssxrxp.mm"
include "sstri.mm"
include "fss.mm"
include "sylancl.mm"
include "fco.mm"
include "sylancr.mm"
include "frn.mm"
include "syl.mm"
include "sspwuni.mm"
include "sylib.mm"
include "wa.mm"
include "crp.mm"
include "c4.mm"
include "c2.mm"
include "cdiv.mm"
include "cmul.mm"
include "cabs.mm"
include "cmin.mm"
include "c1.mm"
include "cseq.mm"
include "clt.mm"
include "csup.mm"
include "cmap.mm"
include "wrex.mm"
include "elpwi.mm"
include "ad2antrl.mm"
include "adantr.mm"
include "simprr.mm"
include "rphalfcl.mm"
include "rphalfcld.mm"
include "adantl.mm"
include "eqid.mm"
include "ovolgelb.mm"
include "syl3anc.mm"
include "ad3antrrr.mm"
include "wdisj.mm"
include "elmapi.mm"
include "simprrl.mm"
include "simprrr.mm"
include "uniioombllem6.mm"
include "rexlimddv.mm"
include "cc.mm"
include "rpcn.mm"
include "2cnd.mm"
include "cc0.mm"
include "wne.mm"
include "2ne0.mm"
include "a1i.mm"
include "divdiv1d.mm"
include "2t2e4.mm"
include "oveq2i.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "4cn.mm"
include "4ne0.mm"
include "divcan2d.mm"
include "eqtrd.mm"
include "breqtrd.mm"
include "ralrimiva.mm"
include "wb.mm"
include "inss1.mm"
include "ovolsscl.mm"
include "difssd.mm"
include "readdcld.mm"
include "alrple.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "expr.mm"
include "ismbl2.mm"
include "sylanbrc.mm"

theorem uniioombl
  let wph: wff ph
  let vx: setvar x
  let cS: class S
  let cF: class F
  let va: setvar a
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vn: setvar n
  let vr: setvar r
  let vy: setvar y
  let vz: setvar z
  let vm: setvar m
  let vw: setvar w
  let cG: class G
  let cK: class K
  let cA: class A
  let cC: class C
  let cM: class M
  let cE: class E
  let cH: class H
  let cJ: class J
  let cN: class N
  let cT: class T
  assume uniioombl.1: |- ( ph -> F : NN --> ( <_ i^i ( RR X. RR ) ) )
  assume uniioombl.2: |- ( ph -> Disj_ x e. NN ( (,) ` ( F ` x ) ) )
  assume uniioombl.3: |- S = seq 1 ( + , ( ( abs o. - ) o. F ) )

  disjoint F x
  disjoint ph x
  disjoint a f
  disjoint a i
  disjoint a j
  disjoint a k
  disjoint a n
  disjoint a r
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint F a
  disjoint f i
  disjoint f j
  disjoint f k
  disjoint f n
  disjoint f r
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint F f
  disjoint i j
  disjoint i k
  disjoint i n
  disjoint i r
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint F i
  disjoint j k
  disjoint j n
  disjoint j r
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint F j
  disjoint k n
  disjoint k r
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint F k
  disjoint n r
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint F r
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint a m
  disjoint a w
  disjoint G a
  disjoint i m
  disjoint i w
  disjoint G i
  disjoint j m
  disjoint j w
  disjoint G j
  disjoint k m
  disjoint k w
  disjoint G k
  disjoint m n
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint G m
  disjoint n w
  disjoint G n
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint G w
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint K j
  disjoint K n
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint A a
  disjoint A j
  disjoint A k
  disjoint A m
  disjoint A n
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint C a
  disjoint C i
  disjoint C j
  disjoint C k
  disjoint C m
  disjoint C n
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint M i
  disjoint M j
  disjoint M k
  disjoint M n
  disjoint M w
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint E m
  disjoint E n
  disjoint H n
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint J n
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint N i
  disjoint N j
  disjoint N n
  disjoint N z
  disjoint S n
  disjoint S y
  disjoint a ph
  disjoint f m
  disjoint f ph
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint m r
  disjoint m ph
  disjoint n ph
  disjoint ph r
  disjoint ph y
  disjoint ph z
  disjoint T a
  disjoint T i
  disjoint T j
  disjoint T k
  disjoint T m
  disjoint T n
  disjoint T x
  disjoint T y
  disjoint T z
  assert |- ( ph -> U. ran ( (,) o. F ) e. dom vol )

  proof
    wph
    cioo
    cF
    ccom
    #
    crn
    #
    cuni
    #
    cr
    wss
    #
    vz
    cv
    #
    covol
    cfv
    #
    cr
    wcel
    #
    @4
    @2
    cin
    #
    covol
    cfv
    #
    @4
    @2
    cdif
    #
    covol
    cfv
    #
    caddc
    co
    #
    @5
    cle
    wbr
    #
    wi
    #
    vz
    cr
    cpw
    #
    wral
    @2
    cvol
    cdm
    wcel
    wph
    @1
    @14
    wss
    #
    @3
    wph
    cn
    @14
    @0
    wf
    #
    @15
    wph
    cxr
    cxr
    cxp
    #
    @14
    cioo
    wf
    cn
    @17
    cF
    wf
    #
    @16
    ioof
    wph
    cn
    cle
    cr
    cr
    cxp
    #
    cin
    #
    cF
    wf
    #
    @20
    @17
    wss
    @18
    uniioombl.1
    @20
    @19
    @17
    cle
    @19
    inss2
    rexpssxrxp
    sstri
    cn
    @20
    @17
    cF
    fss
    sylancl
    cn
    @17
    @14
    cioo
    cF
    fco
    sylancr
    cn
    @14
    @0
    frn
    syl
    @1
    cr
    sspwuni
    sylib
    wph
    @13
    vz
    @14
    wph
    @4
    @14
    wcel
    #
    @6
    @12
    wph
    @22
    @6
    wa
    #
    wa
    #
    @12
    @11
    @5
    vr
    cv
    #
    caddc
    co
    #
    cle
    wbr
    #
    vr
    crp
    wral
    #
    @24
    @27
    vr
    crp
    @24
    @25
    crp
    wcel
    #
    wa
    #
    @11
    @5
    c4
    @25
    c2
    cdiv
    co
    #
    c2
    cdiv
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    @26
    cle
    @30
    @4
    cioo
    vf
    cv
    #
    ccom
    crn
    cuni
    wss
    #
    caddc
    cabs
    cmin
    ccom
    @35
    ccom
    c1
    cseq
    #
    crn
    cxr
    clt
    csup
    @5
    @32
    caddc
    co
    cle
    wbr
    #
    wa
    #
    @11
    @34
    cle
    wbr
    vf
    @20
    cn
    cmap
    co
    #
    @30
    @4
    cr
    wss
    #
    @6
    @32
    crp
    wcel
    #
    @39
    vf
    @40
    wrex
    @24
    @41
    @29
    @22
    @41
    wph
    @6
    @4
    cr
    elpwi
    ad2antrl
    #
    adantr
    @24
    @6
    @29
    wph
    @22
    @6
    simprr
    #
    adantr
    #
    @29
    @42
    @24
    @29
    @31
    @25
    rphalfcl
    #
    rphalfcld
    adantl
    @4
    @32
    @37
    vf
    @37
    eqid
    #
    ovolgelb
    syl3anc
    @30
    @35
    @40
    wcel
    #
    @39
    wa
    #
    wa
    #
    vx
    @2
    @32
    cS
    @37
    @4
    cF
    @35
    wph
    @21
    @23
    @29
    @49
    uniioombl.1
    ad3antrrr
    wph
    vx
    cn
    vx
    cv
    cF
    cfv
    cioo
    cfv
    wdisj
    @23
    @29
    @49
    uniioombl.2
    ad3antrrr
    uniioombl.3
    @2
    eqid
    @30
    @6
    @49
    @45
    adantr
    @50
    @31
    @30
    @31
    crp
    wcel
    #
    @49
    @29
    @51
    @24
    @46
    adantl
    adantr
    rphalfcld
    @48
    cn
    @20
    @35
    wf
    @30
    @39
    @35
    @20
    cn
    elmapi
    ad2antrl
    @30
    @48
    @36
    @38
    simprrl
    @47
    @30
    @48
    @36
    @38
    simprrr
    uniioombllem6
    rexlimddv
    @30
    @33
    @25
    @5
    caddc
    @30
    @33
    c4
    @25
    c4
    cdiv
    co
    #
    cmul
    co
    @25
    @30
    @32
    @52
    c4
    cmul
    @30
    @32
    @25
    c2
    c2
    cmul
    co
    #
    cdiv
    co
    @52
    @30
    @25
    c2
    c2
    @29
    @25
    cc
    wcel
    @24
    @25
    rpcn
    adantl
    #
    @30
    2cnd
    #
    @55
    c2
    cc0
    wne
    @30
    2ne0
    a1i
    #
    @56
    divdiv1d
    @53
    c4
    @25
    cdiv
    2t2e4
    oveq2i
    syl6eq
    oveq2d
    @30
    @25
    c4
    @54
    c4
    cc
    wcel
    @30
    4cn
    a1i
    c4
    cc0
    wne
    @30
    4ne0
    a1i
    divcan2d
    eqtrd
    oveq2d
    breqtrd
    ralrimiva
    @24
    @11
    cr
    wcel
    @6
    @12
    @28
    wb
    @24
    @8
    @10
    @24
    @7
    @4
    wss
    #
    @41
    @6
    @8
    cr
    wcel
    @57
    @24
    @4
    @2
    inss1
    a1i
    @43
    @44
    @7
    @4
    ovolsscl
    syl3anc
    @24
    @9
    @4
    wss
    @41
    @6
    @10
    cr
    wcel
    @24
    @4
    @2
    difssd
    @43
    @44
    @9
    @4
    ovolsscl
    syl3anc
    readdcld
    @44
    vr
    @11
    @5
    alrple
    syl2anc
    mpbird
    expr
    ralrimiva
    vz
    @2
    ismbl2
    sylanbrc
end
