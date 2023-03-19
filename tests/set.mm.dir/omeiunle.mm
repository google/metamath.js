include "cv.mm"
include "cfv.mm"
include "ciun.mm"
include "crn.mm"
include "cres.mm"
include "csumge0.mm"
include "cmpt.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "cxr.mm"
include "iccssxr.mm"
include "wss.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "cpw.mm"
include "ffvelrnda.mm"
include "elpwi.mm"
include "syl.mm"
include "ex.mm"
include "ralrimi.mm"
include "iunss.mm"
include "sylibr.mm"
include "omecl.mm"
include "sseldi.mm"
include "cvv.mm"
include "wfn.mm"
include "ffnd.mm"
include "cuz.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "fnex.mm"
include "syl2anc.mm"
include "rnexg.mm"
include "omef.mm"
include "wf.mm"
include "frn.mm"
include "fssresd.mm"
include "sge0xrcl.mm"
include "come.mm"
include "adantr.mm"
include "eqid.mm"
include "fmptdf.mm"
include "cuni.mm"
include "cle.mm"
include "wceq.mm"
include "rgenw.mm"
include "dfiun3g.mm"
include "ax-mp.mm"
include "feqmptd.mm"
include "nfcv.mm"
include "nffv.mm"
include "fveq2.mm"
include "cbvmpt.mm"
include "eqtrd.mm"
include "rneqd.mm"
include "unieqd.mm"
include "eqtr4d.mm"
include "fveq2d.mm"
include "cdom.mm"
include "wbr.mm"
include "com.mm"
include "fnrndomg.mm"
include "sylc.mm"
include "uzct.mm"
include "domtr.mm"
include "omeunile.mm"
include "eqbrtrd.mm"
include "ccom.mm"
include "clt.mm"
include "wwe.mm"
include "ltweuz.mm"
include "wb.mm"
include "weeq2.mm"
include "mpbir.mm"
include "sge0resrn.mm"
include "fcompt.mm"
include "breqtrd.mm"
include "xrletrd.mm"

theorem omeiunle
  let wph: wff ph
  let vn: setvar n
  let cE: class E
  let cN: class N
  let cO: class O
  let cX: class X
  let cZ: class Z
  let vm: setvar m
  let vk: setvar k
  let vx: setvar x
  assume omeiunle.nph: |- F/ n ph
  assume omeiunle.ne: |- F/_ n E
  assume omeiunle.o: |- ( ph -> O e. OutMeas )
  assume omeiunle.x: |- X = U. dom O
  assume omeiunle.z: |- Z = ( ZZ>= ` N )
  assume omeiunle.e: |- ( ph -> E : Z --> ~P X )

  disjoint O n
  disjoint X n
  disjoint Z n
  disjoint E m
  disjoint O m
  disjoint m n
  disjoint X m
  disjoint Z m
  disjoint k x
  assert |- ( ph -> ( O ` U_ n e. Z ( E ` n ) ) <_ ( sum^ ` ( n e. Z |-> ( O ` ( E ` n ) ) ) ) )

  proof
    wph
    vn
    cZ
    vn
    cv
    #
    cE
    cfv
    #
    ciun
    #
    cO
    cfv
    #
    cO
    cE
    crn
    #
    cres
    #
    csumge0
    cfv
    #
    vn
    cZ
    @1
    cO
    cfv
    #
    cmpt
    #
    csumge0
    cfv
    #
    wph
    cc0
    cpnf
    cicc
    co
    #
    cxr
    @3
    cc0
    cpnf
    iccssxr
    wph
    @2
    cO
    cX
    omeiunle.o
    omeiunle.x
    wph
    @1
    cX
    wss
    #
    vn
    cZ
    wral
    @2
    cX
    wss
    wph
    @11
    vn
    cZ
    omeiunle.nph
    wph
    @0
    cZ
    wcel
    #
    @11
    wph
    @12
    wa
    #
    @1
    cX
    cpw
    #
    wcel
    @11
    wph
    cZ
    @14
    @0
    cE
    omeiunle.e
    ffvelrnda
    @1
    cX
    elpwi
    syl
    #
    ex
    ralrimi
    vn
    cZ
    @1
    cX
    iunss
    sylibr
    omecl
    sseldi
    wph
    @5
    cvv
    @4
    wph
    cE
    cvv
    wcel
    #
    @4
    cvv
    wcel
    wph
    cE
    cZ
    wfn
    #
    cZ
    cvv
    wcel
    #
    @16
    wph
    cZ
    @14
    cE
    omeiunle.e
    ffnd
    #
    @18
    wph
    cZ
    cN
    cuz
    cfv
    #
    cvv
    omeiunle.z
    cN
    cuz
    fvex
    eqeltri
    a1i
    #
    cZ
    cvv
    cE
    fnex
    syl2anc
    cE
    cvv
    rnexg
    syl
    wph
    @14
    @10
    @4
    cO
    wph
    cO
    cX
    omeiunle.o
    omeiunle.x
    omef
    #
    wph
    cZ
    @14
    cE
    wf
    #
    @4
    @14
    wss
    omeiunle.e
    cZ
    @14
    cE
    frn
    syl
    #
    fssresd
    sge0xrcl
    wph
    @8
    cvv
    cZ
    @21
    wph
    vn
    cZ
    @7
    @10
    @8
    omeiunle.nph
    @13
    @1
    cO
    cX
    wph
    cO
    come
    wcel
    @12
    omeiunle.o
    adantr
    omeiunle.x
    @15
    omecl
    @8
    eqid
    fmptdf
    sge0xrcl
    wph
    @3
    @4
    cuni
    #
    cO
    cfv
    @6
    cle
    wph
    @2
    @25
    cO
    wph
    @2
    vn
    cZ
    @1
    cmpt
    #
    crn
    #
    cuni
    #
    @25
    @2
    @28
    wceq
    #
    wph
    @1
    cvv
    wcel
    #
    vn
    cZ
    wral
    @29
    @30
    vn
    cZ
    @0
    cE
    fvex
    rgenw
    vn
    cZ
    @1
    cvv
    dfiun3g
    ax-mp
    a1i
    wph
    @4
    @27
    wph
    cE
    @26
    wph
    cE
    vm
    cZ
    vm
    cv
    #
    cE
    cfv
    #
    cmpt
    #
    @26
    wph
    vm
    cZ
    @14
    cE
    omeiunle.e
    feqmptd
    @33
    @26
    wceq
    wph
    vm
    vn
    cZ
    @32
    @1
    vn
    @31
    cE
    omeiunle.ne
    vn
    @31
    nfcv
    nffv
    #
    vm
    @1
    nfcv
    @31
    @0
    cE
    fveq2
    #
    cbvmpt
    a1i
    eqtrd
    rneqd
    unieqd
    eqtr4d
    fveq2d
    wph
    cO
    cX
    @4
    omeiunle.o
    omeiunle.x
    @24
    wph
    @4
    cZ
    cdom
    wbr
    #
    cZ
    com
    cdom
    wbr
    #
    @4
    com
    cdom
    wbr
    wph
    @18
    @17
    @36
    @21
    @19
    cZ
    cvv
    cE
    fnrndomg
    sylc
    @37
    wph
    cN
    cZ
    omeiunle.z
    uzct
    a1i
    @4
    cZ
    com
    domtr
    syl2anc
    omeunile
    eqbrtrd
    wph
    @6
    cO
    cE
    ccom
    #
    csumge0
    cfv
    @9
    cle
    wph
    cZ
    @14
    clt
    cO
    cE
    cvv
    @21
    @22
    omeiunle.e
    cZ
    clt
    wwe
    #
    wph
    @39
    @20
    clt
    wwe
    #
    cN
    ltweuz
    cZ
    @20
    wceq
    @39
    @40
    wb
    omeiunle.z
    cZ
    @20
    clt
    weeq2
    ax-mp
    mpbir
    a1i
    sge0resrn
    wph
    @38
    @8
    csumge0
    wph
    @14
    @10
    cO
    wf
    #
    @23
    @38
    @8
    wceq
    @22
    omeiunle.e
    @41
    @23
    wa
    #
    @38
    vm
    cZ
    @32
    cO
    cfv
    #
    cmpt
    #
    @8
    vm
    cO
    cE
    cZ
    @14
    @10
    fcompt
    @44
    @8
    wceq
    @42
    vm
    vn
    cZ
    @43
    @7
    vn
    @32
    cO
    vn
    cO
    nfcv
    @34
    nffv
    vm
    @7
    nfcv
    @31
    @0
    wceq
    @32
    @1
    cO
    @35
    fveq2d
    cbvmpt
    a1i
    eqtrd
    syl2anc
    fveq2d
    breqtrd
    xrletrd
end
