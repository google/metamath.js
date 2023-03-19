include "cpw.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wss.mm"
include "cvv.mm"
include "wb.mm"
include "come.mm"
include "unidmex.mm"
include "ssexd.mm"
include "elpwg.mm"
include "syl.mm"
include "mpbird.mm"
include "cdm.mm"
include "cuni.mm"
include "syl6sseq.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "wceq.mm"
include "wa.mm"
include "c0.mm"
include "com.mm"
include "cdom.mm"
include "cres.mm"
include "csumge0.mm"
include "wi.mm"
include "isome.mm"
include "mpbid.mm"
include "simplrd.mm"
include "pweq.mm"
include "raleqdv.mm"
include "fveq2.mm"
include "breq2d.mm"
include "ralbidv.mm"
include "bitrd.mm"
include "rspcva.mm"
include "syl2anc.mm"
include "breq1d.mm"

theorem omessle
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cO: class O
  let cX: class X
  let vz: setvar z
  let vy: setvar y
  let vk: setvar k
  let vx: setvar x
  assume omessle.o: |- ( ph -> O e. OutMeas )
  assume omessle.x: |- X = U. dom O
  assume omessle.b: |- ( ph -> B C_ X )
  assume omessle.a: |- ( ph -> A C_ B )


  assert |- ( ph -> ( O ` A ) <_ ( O ` B ) )

  proof
    wph
    cA
    cB
    cpw
    #
    wcel
    #
    vz
    cv
    #
    cO
    cfv
    #
    cB
    cO
    cfv
    #
    cle
    wbr
    #
    vz
    @0
    wral
    #
    cA
    cO
    cfv
    #
    @4
    cle
    wbr
    #
    wph
    @1
    cA
    cB
    wss
    #
    omessle.a
    wph
    cA
    cvv
    wcel
    @1
    @9
    wb
    wph
    cA
    cB
    cvv
    wph
    cB
    cX
    cvv
    wph
    cO
    come
    cX
    omessle.o
    omessle.x
    unidmex
    omessle.b
    ssexd
    #
    omessle.a
    ssexd
    cA
    cB
    cvv
    elpwg
    syl
    mpbird
    wph
    cB
    cO
    cdm
    #
    cuni
    #
    cpw
    #
    wcel
    #
    @3
    vy
    cv
    #
    cO
    cfv
    #
    cle
    wbr
    #
    vz
    @15
    cpw
    #
    wral
    #
    vy
    @13
    wral
    #
    @6
    wph
    @14
    cB
    @12
    wss
    #
    wph
    cB
    cX
    @12
    omessle.b
    omessle.x
    syl6sseq
    wph
    cB
    cvv
    wcel
    @14
    @21
    wb
    @10
    cB
    @12
    cvv
    elpwg
    syl
    mpbird
    wph
    @11
    cc0
    cpnf
    cicc
    co
    cO
    wf
    @11
    @13
    wceq
    wa
    c0
    cO
    cfv
    cc0
    wceq
    wa
    #
    @20
    @15
    com
    cdom
    wbr
    @15
    cuni
    cO
    cfv
    cO
    @15
    cres
    csumge0
    cfv
    cle
    wbr
    wi
    vy
    @11
    cpw
    wral
    #
    wph
    cO
    come
    wcel
    #
    @22
    @20
    wa
    @23
    wa
    #
    omessle.o
    wph
    @24
    @24
    @25
    wb
    omessle.o
    vy
    vz
    cO
    come
    isome
    syl
    mpbid
    simplrd
    @19
    @6
    vy
    cB
    @13
    @15
    cB
    wceq
    #
    @19
    @17
    vz
    @0
    wral
    @6
    @26
    @17
    vz
    @18
    @0
    @15
    cB
    pweq
    raleqdv
    @26
    @17
    @5
    vz
    @0
    @26
    @16
    @4
    @3
    cle
    @15
    cB
    cO
    fveq2
    breq2d
    ralbidv
    bitrd
    rspcva
    syl2anc
    @5
    @8
    vz
    cA
    @0
    @2
    cA
    wceq
    @3
    @7
    @4
    cle
    @2
    cA
    cO
    fveq2
    breq1d
    rspcva
    syl2anc
end
