include "cicc.mm"
include "ccom.mm"
include "crn.mm"
include "cuni.mm"
include "covol.mm"
include "cfv.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "cn.mm"
include "cr.mm"
include "cxp.mm"
include "cin.mm"
include "wf.mm"
include "wss.mm"
include "ssid.mm"
include "ovollb2.mm"
include "sylancl.mm"
include "cioo.mm"
include "uniioovol.mm"
include "cv.mm"
include "ciun.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "c1st.mm"
include "c2nd.mm"
include "cop.mm"
include "co.mm"
include "ioossicc.mm"
include "df-ov.mm"
include "3sstr3i.mm"
include "a1i.mm"
include "inss2.mm"
include "ffvelrn.mm"
include "sseldi.mm"
include "1st2nd2.mm"
include "syl.mm"
include "fveq2d.mm"
include "3sstr4d.mm"
include "fvco3.mm"
include "sylan.mm"
include "ralrimiva.mm"
include "ss2iun.mm"
include "wfn.mm"
include "cpw.mm"
include "ioof.mm"
include "ffn.mm"
include "ax-mp.mm"
include "rexpssxrxp.mm"
include "sstri.mm"
include "fss.mm"
include "fnfco.mm"
include "sylancr.mm"
include "fniunfv.mm"
include "iccf.mm"
include "3sstr3d.mm"
include "ovolficcss.mm"
include "ovolss.mm"
include "syl2anc.mm"
include "eqbrtrrd.mm"
include "wb.mm"
include "ovolcl.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "cabs.mm"
include "cmin.mm"
include "eqid.mm"
include "ovolsf.mm"
include "frn.mm"
include "icossxr.mm"
include "syl6ss.mm"
include "supxrcl.mm"
include "xrletri3.mm"
include "mpbir2and.mm"

theorem uniiccvol
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
  assert |- ( ph -> ( vol* ` U. ran ( [,] o. F ) ) = sup ( ran S , RR* , < ) )

  proof
    wph
    cicc
    cF
    ccom
    #
    crn
    cuni
    #
    covol
    cfv
    #
    cS
    crn
    #
    cxr
    clt
    csup
    #
    wceq
    #
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
    @1
    @1
    wss
    @6
    uniioombl.1
    @1
    ssid
    @1
    cS
    cF
    uniioombl.3
    ovollb2
    sylancl
    wph
    cioo
    cF
    ccom
    #
    crn
    cuni
    #
    covol
    cfv
    #
    @4
    @2
    cle
    wph
    vx
    cS
    cF
    uniioombl.1
    uniioombl.2
    uniioombl.3
    uniioovol
    wph
    @12
    @1
    wss
    @1
    cr
    wss
    #
    @13
    @2
    cle
    wbr
    wph
    vx
    cn
    vx
    cv
    #
    @11
    cfv
    #
    ciun
    #
    vx
    cn
    @15
    @0
    cfv
    #
    ciun
    #
    @12
    @1
    wph
    @16
    @18
    wss
    #
    vx
    cn
    wral
    @17
    @19
    wss
    wph
    @20
    vx
    cn
    wph
    @10
    @15
    cn
    wcel
    #
    @20
    uniioombl.1
    @10
    @21
    wa
    #
    @15
    cF
    cfv
    #
    cioo
    cfv
    #
    @23
    cicc
    cfv
    #
    @16
    @18
    @22
    @23
    c1st
    cfv
    #
    @23
    c2nd
    cfv
    #
    cop
    #
    cioo
    cfv
    #
    @28
    cicc
    cfv
    #
    @24
    @25
    @29
    @30
    wss
    @22
    @26
    @27
    cioo
    co
    @26
    @27
    cicc
    co
    @29
    @30
    @26
    @27
    ioossicc
    @26
    @27
    cioo
    df-ov
    @26
    @27
    cicc
    df-ov
    3sstr3i
    a1i
    @22
    @23
    @28
    cioo
    @22
    @23
    @8
    wcel
    @23
    @28
    wceq
    @22
    @9
    @8
    @23
    cle
    @8
    inss2
    #
    cn
    @9
    @15
    cF
    ffvelrn
    sseldi
    @23
    cr
    cr
    1st2nd2
    syl
    #
    fveq2d
    @22
    @23
    @28
    cicc
    @32
    fveq2d
    3sstr4d
    cn
    @9
    @15
    cioo
    cF
    fvco3
    cn
    @9
    @15
    cicc
    cF
    fvco3
    3sstr4d
    sylan
    ralrimiva
    vx
    cn
    @16
    @18
    ss2iun
    syl
    wph
    @11
    cn
    wfn
    #
    @17
    @12
    wceq
    wph
    cioo
    cxr
    cxr
    cxp
    #
    wfn
    #
    cn
    @34
    cF
    wf
    #
    @33
    @34
    cr
    cpw
    #
    cioo
    wf
    @35
    ioof
    @34
    @37
    cioo
    ffn
    ax-mp
    wph
    @10
    @9
    @34
    wss
    @36
    uniioombl.1
    @9
    @8
    @34
    @31
    rexpssxrxp
    sstri
    cn
    @9
    @34
    cF
    fss
    sylancl
    #
    @34
    cn
    cioo
    cF
    fnfco
    sylancr
    vx
    cn
    @11
    fniunfv
    syl
    wph
    @0
    cn
    wfn
    #
    @19
    @1
    wceq
    wph
    cicc
    @34
    wfn
    #
    @36
    @39
    @34
    cxr
    cpw
    #
    cicc
    wf
    @40
    iccf
    @34
    @41
    cicc
    ffn
    ax-mp
    @38
    @34
    cn
    cicc
    cF
    fnfco
    sylancr
    vx
    cn
    @0
    fniunfv
    syl
    3sstr3d
    wph
    @10
    @14
    uniioombl.1
    cF
    ovolficcss
    syl
    #
    @12
    @1
    ovolss
    syl2anc
    eqbrtrrd
    wph
    @2
    cxr
    wcel
    #
    @4
    cxr
    wcel
    #
    @5
    @6
    @7
    wa
    wb
    wph
    @14
    @43
    @42
    @1
    ovolcl
    syl
    wph
    @3
    cxr
    wss
    @44
    wph
    @3
    cc0
    cpnf
    cico
    co
    #
    cxr
    wph
    cn
    @45
    cS
    wf
    #
    @3
    @45
    wss
    wph
    @10
    @46
    uniioombl.1
    cS
    cF
    cabs
    cmin
    ccom
    cF
    ccom
    #
    @47
    eqid
    uniioombl.3
    ovolsf
    syl
    cn
    @45
    cS
    frn
    syl
    cc0
    cpnf
    icossxr
    syl6ss
    @3
    supxrcl
    syl
    @2
    @4
    xrletri3
    syl2anc
    mpbir2and
end
