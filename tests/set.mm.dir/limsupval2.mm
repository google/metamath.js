include "clsp.mm"
include "cfv.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "cinf.mm"
include "cima.mm"
include "wcel.mm"
include "wceq.mm"
include "limsupval.mm"
include "syl.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "wral.mm"
include "wss.mm"
include "imassrn.mm"
include "cr.mm"
include "wf.mm"
include "limsupgf.mm"
include "frn.mm"
include "ax-mp.mm"
include "infxrlb.mm"
include "ralrimiva.mm"
include "mp1i.mm"
include "ssralv.mm"
include "mpsyl.mm"
include "wb.mm"
include "sstri.mm"
include "infxrcl.mm"
include "infxrgelb.mm"
include "mp2an.mm"
include "sylibr.mm"
include "wrex.mm"
include "csup.mm"
include "cpnf.mm"
include "ressxr.mm"
include "syl6ss.mm"
include "supxrunb1.mm"
include "mpbird.mm"
include "wa.mm"
include "sselda.mm"
include "ad2ant2r.mm"
include "ffvelrni.mm"
include "ad2antlr.mm"
include "wfn.mm"
include "ffn.mm"
include "ad2antrr.mm"
include "simprl.mm"
include "fnfvima.mm"
include "syl3anc.mm"
include "sylancr.mm"
include "cico.mm"
include "co.mm"
include "cin.mm"
include "simplr.mm"
include "simprr.mm"
include "limsupgord.mm"
include "limsupgval.mm"
include "3brtr4d.mm"
include "xrletrd.mm"
include "rexlimdvaa.mm"
include "ralimdva.mm"
include "mpd.mm"
include "breq2.mm"
include "ralrn.mm"
include "xrletri3.mm"
include "sylanbrc.mm"
include "eqtrd.mm"

theorem limsupval2
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cV: class V
  let vn: setvar n
  let vx: setvar x
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let vf: setvar f
  let cM: class M
  let vj: setvar j
  let cC: class C
  assume limsupval.1: |- G = ( k e. RR |-> sup ( ( ( F " ( k [,) +oo ) ) i^i RR* ) , RR* , < ) )
  assume limsupval2.1: |- ( ph -> F e. V )
  assume limsupval2.2: |- ( ph -> A C_ RR )
  assume limsupval2.3: |- ( ph -> sup ( A , RR* , < ) = +oo )

  disjoint A k
  disjoint F k
  disjoint A n
  disjoint A x
  disjoint k n
  disjoint k x
  disjoint n x
  disjoint G n
  disjoint n ph
  disjoint ph x
  disjoint k x
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint F x
  disjoint f k
  disjoint G x
  disjoint M k
  disjoint A j
  disjoint B j
  disjoint C j
  disjoint C k
  disjoint C x
  disjoint j k
  disjoint j x
  disjoint F j
  disjoint G j
  assert |- ( ph -> ( limsup ` F ) = inf ( ( G " A ) , RR* , < ) )

  proof
    wph
    cF
    clsp
    cfv
    #
    cG
    crn
    #
    cxr
    clt
    cinf
    #
    cG
    cA
    cima
    #
    cxr
    clt
    cinf
    #
    wph
    cF
    cV
    wcel
    @0
    @2
    wceq
    limsupval2.1
    vk
    cF
    cG
    cV
    limsupval.1
    limsupval
    syl
    wph
    @2
    @4
    cle
    wbr
    #
    @4
    @2
    cle
    wbr
    #
    @2
    @4
    wceq
    #
    wph
    @2
    vx
    cv
    #
    cle
    wbr
    #
    vx
    @3
    wral
    #
    @5
    @3
    @1
    wss
    wph
    @9
    vx
    @1
    wral
    #
    @10
    cG
    cA
    imassrn
    #
    @1
    cxr
    wss
    #
    @11
    wph
    cr
    cxr
    cG
    wf
    #
    @13
    vk
    cF
    cG
    limsupval.1
    limsupgf
    #
    cr
    cxr
    cG
    frn
    ax-mp
    #
    @13
    @9
    vx
    @1
    @1
    @8
    infxrlb
    ralrimiva
    mp1i
    @9
    vx
    @3
    @1
    ssralv
    mpsyl
    @3
    cxr
    wss
    #
    @2
    cxr
    wcel
    #
    @5
    @10
    wb
    @3
    @1
    cxr
    @12
    @16
    sstri
    #
    @13
    @18
    @16
    @1
    infxrcl
    ax-mp
    #
    vx
    @3
    @2
    infxrgelb
    mp2an
    sylibr
    wph
    @4
    @8
    cle
    wbr
    #
    vx
    @1
    wral
    #
    @6
    wph
    @4
    vn
    cv
    #
    cG
    cfv
    #
    cle
    wbr
    #
    vn
    cr
    wral
    #
    @22
    wph
    @23
    @8
    cle
    wbr
    #
    vx
    cA
    wrex
    #
    vn
    cr
    wral
    #
    @26
    wph
    @29
    cA
    cxr
    clt
    csup
    cpnf
    wceq
    #
    limsupval2.3
    wph
    cA
    cxr
    wss
    @29
    @30
    wb
    wph
    cA
    cr
    cxr
    limsupval2.2
    ressxr
    syl6ss
    vn
    vx
    cA
    supxrunb1
    syl
    mpbird
    wph
    @28
    @25
    vn
    cr
    wph
    @23
    cr
    wcel
    #
    wa
    #
    @27
    @25
    vx
    cA
    @32
    @8
    cA
    wcel
    #
    @27
    wa
    #
    wa
    #
    @4
    @8
    cG
    cfv
    #
    @24
    @17
    @4
    cxr
    wcel
    #
    @35
    @19
    @3
    infxrcl
    #
    mp1i
    @35
    @8
    cr
    wcel
    #
    @36
    cxr
    wcel
    wph
    @33
    @39
    @31
    @27
    wph
    cA
    cr
    @8
    limsupval2.2
    sselda
    ad2ant2r
    #
    cr
    cxr
    @8
    cG
    @15
    ffvelrni
    syl
    @31
    @24
    cxr
    wcel
    wph
    @34
    cr
    cxr
    @23
    cG
    @15
    ffvelrni
    ad2antlr
    @35
    @17
    @36
    @3
    wcel
    #
    @4
    @36
    cle
    wbr
    @19
    @35
    cG
    cr
    wfn
    #
    cA
    cr
    wss
    #
    @33
    @41
    @14
    @42
    @35
    @15
    cr
    cxr
    cG
    ffn
    #
    mp1i
    wph
    @43
    @31
    @34
    limsupval2.2
    ad2antrr
    @32
    @33
    @27
    simprl
    cr
    cA
    cG
    @8
    fnfvima
    syl3anc
    @3
    @36
    infxrlb
    sylancr
    @35
    cF
    @8
    cpnf
    cico
    co
    cima
    cxr
    cin
    cxr
    clt
    csup
    #
    cF
    @23
    cpnf
    cico
    co
    cima
    cxr
    cin
    cxr
    clt
    csup
    #
    @36
    @24
    cle
    @35
    @31
    @39
    @27
    @45
    @46
    cle
    wbr
    wph
    @31
    @34
    simplr
    @40
    @32
    @33
    @27
    simprr
    @23
    @8
    cF
    limsupgord
    syl3anc
    @35
    @39
    @36
    @45
    wceq
    @40
    vk
    cF
    cG
    @8
    limsupval.1
    limsupgval
    syl
    @31
    @24
    @46
    wceq
    wph
    @34
    vk
    cF
    cG
    @23
    limsupval.1
    limsupgval
    ad2antlr
    3brtr4d
    xrletrd
    rexlimdvaa
    ralimdva
    mpd
    @42
    @22
    @26
    wb
    @14
    @42
    @15
    @44
    ax-mp
    @21
    @25
    vx
    vn
    cr
    cG
    @8
    @24
    @4
    cle
    breq2
    ralrn
    ax-mp
    sylibr
    @13
    @37
    @6
    @22
    wb
    @16
    @17
    @37
    @19
    @38
    ax-mp
    #
    vx
    @1
    @4
    infxrgelb
    mp2an
    sylibr
    @18
    @37
    @7
    @5
    @6
    wa
    wb
    @20
    @47
    @2
    @4
    xrletri3
    mp2an
    sylanbrc
    eqtrd
end
