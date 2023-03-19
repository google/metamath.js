include "cun.mm"
include "cfv.mm"
include "cpr.mm"
include "cuni.mm"
include "cxad.mm"
include "co.mm"
include "cle.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "wss.mm"
include "come.mm"
include "unidmex.mm"
include "ssexg.mm"
include "syl2anc.mm"
include "uniprg.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "cres.mm"
include "csumge0.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "cxr.mm"
include "iccssxr.mm"
include "unssd.mm"
include "eqsstrd.mm"
include "omecl.mm"
include "sseldi.mm"
include "cfn.mm"
include "prfi.mm"
include "elexi.mm"
include "a1i.mm"
include "cpw.mm"
include "omef.mm"
include "wa.mm"
include "wb.mm"
include "elpwg.mm"
include "syl.mm"
include "mpbird.mm"
include "jca.mm"
include "prssg.mm"
include "mpbid.mm"
include "fssresd.mm"
include "sge0xrcl.mm"
include "xaddcld.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "csdm.mm"
include "isfinite.mm"
include "biimpi.mm"
include "sdomdom.mm"
include "ax-mp.mm"
include "omeunile.mm"
include "cv.mm"
include "cmpt.mm"
include "feqresmpt.mm"
include "fveq2.mm"
include "sge0prle.mm"
include "eqbrtrd.mm"
include "xrletrd.mm"

theorem omeunle
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cO: class O
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume omeunle.o: |- ( ph -> O e. OutMeas )
  assume omeunle.x: |- X = U. dom O
  assume omeunle.a: |- ( ph -> A C_ X )
  assume omeunle.b: |- ( ph -> B C_ X )


  assert |- ( ph -> ( O ` ( A u. B ) ) <_ ( ( O ` A ) +e ( O ` B ) ) )

  proof
    wph
    cA
    cB
    cun
    #
    cO
    cfv
    cA
    cB
    cpr
    #
    cuni
    #
    cO
    cfv
    #
    cA
    cO
    cfv
    #
    cB
    cO
    cfv
    #
    cxad
    co
    #
    cle
    wph
    @0
    @2
    cO
    wph
    @2
    @0
    wph
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    @2
    @0
    wceq
    wph
    cA
    cX
    wss
    #
    cX
    cvv
    wcel
    #
    @7
    omeunle.a
    wph
    cO
    come
    cX
    omeunle.o
    omeunle.x
    unidmex
    #
    cA
    cX
    cvv
    ssexg
    syl2anc
    #
    wph
    cB
    cX
    wss
    #
    @10
    @8
    omeunle.b
    @11
    cB
    cX
    cvv
    ssexg
    syl2anc
    #
    cA
    cB
    cvv
    cvv
    uniprg
    syl2anc
    #
    eqcomd
    fveq2d
    wph
    @3
    cO
    @1
    cres
    #
    csumge0
    cfv
    #
    @6
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
    #
    wph
    @2
    cO
    cX
    omeunle.o
    omeunle.x
    wph
    @2
    @0
    cX
    @15
    wph
    cA
    cB
    cX
    omeunle.a
    omeunle.b
    unssd
    eqsstrd
    omecl
    sseldi
    wph
    @16
    cvv
    @1
    @1
    cvv
    wcel
    wph
    @1
    cfn
    cA
    cB
    prfi
    #
    elexi
    a1i
    wph
    cX
    cpw
    #
    @18
    @1
    cO
    wph
    cO
    cX
    omeunle.o
    omeunle.x
    omef
    #
    wph
    cA
    @21
    wcel
    #
    cB
    @21
    wcel
    #
    wa
    #
    @1
    @21
    wss
    #
    wph
    @23
    @24
    wph
    @23
    @9
    omeunle.a
    wph
    @7
    @23
    @9
    wb
    @12
    cA
    cX
    cvv
    elpwg
    syl
    mpbird
    wph
    @24
    @13
    omeunle.b
    wph
    @8
    @24
    @13
    wb
    @14
    cB
    cX
    cvv
    elpwg
    syl
    mpbird
    jca
    wph
    @7
    @8
    @25
    @26
    wb
    @12
    @14
    cA
    cB
    @21
    cvv
    cvv
    prssg
    syl2anc
    mpbid
    #
    fssresd
    sge0xrcl
    wph
    @4
    @5
    wph
    @18
    cxr
    @4
    @19
    wph
    cA
    cO
    cX
    omeunle.o
    omeunle.x
    omeunle.a
    omecl
    #
    sseldi
    wph
    @18
    cxr
    @5
    @19
    wph
    cB
    cO
    cX
    omeunle.o
    omeunle.x
    omeunle.b
    omecl
    #
    sseldi
    xaddcld
    wph
    cO
    cX
    @1
    omeunle.o
    omeunle.x
    @27
    @1
    com
    cdom
    wbr
    #
    wph
    @1
    cfn
    wcel
    #
    @30
    @20
    @31
    @1
    com
    csdm
    wbr
    #
    @30
    @31
    @32
    @1
    isfinite
    biimpi
    @1
    com
    sdomdom
    syl
    ax-mp
    a1i
    omeunile
    wph
    @17
    vk
    @1
    vk
    cv
    #
    cO
    cfv
    #
    cmpt
    #
    csumge0
    cfv
    @6
    cle
    wph
    @16
    @35
    csumge0
    wph
    vk
    @21
    @18
    @1
    cO
    @22
    @27
    feqresmpt
    fveq2d
    wph
    cA
    cB
    @34
    @4
    vk
    @5
    cvv
    cvv
    @12
    @14
    @28
    @29
    @33
    cA
    cO
    fveq2
    @33
    cB
    cO
    fveq2
    sge0prle
    eqbrtrd
    xrletrd
    eqbrtrd
end
