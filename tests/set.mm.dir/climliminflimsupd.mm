include "clsi.mm"
include "cfv.mm"
include "clsp.mm"
include "cxr.mm"
include "wcel.mm"
include "cxne.mm"
include "cr.mm"
include "cv.mm"
include "cmpt.mm"
include "feqmptd.mm"
include "fveq2d.mm"
include "cvv.mm"
include "cuz.mm"
include "fvexi.mm"
include "mptex.mm"
include "liminfcl.mm"
include "ax-mp.mm"
include "a1i.mm"
include "eqeltrd.mm"
include "cneg.mm"
include "nfv.mm"
include "wa.mm"
include "ffvelrnda.mm"
include "renegcld.mm"
include "limsupvaluz4.mm"
include "cli.mm"
include "wbr.mm"
include "wceq.mm"
include "cdm.mm"
include "wrel.mm"
include "climrel.mm"
include "nfcv.mm"
include "climlimsup.mm"
include "mpbid.mm"
include "recnd.mm"
include "climneg.mm"
include "releldm.mm"
include "syl2anc.mm"
include "eqid.mm"
include "fmptd.mm"
include "climuni.mm"
include "negnegd.mm"
include "mpteq2dva.mm"
include "eqtr4d.mm"
include "xnegeqd.mm"
include "3eqtr3d.mm"
include "climrecl.mm"
include "eqeltrrd.mm"
include "xnegrecl2.mm"
include "rexnegd.mm"
include "eqtr2d.mm"
include "neg11d.mm"

theorem climliminflimsupd
  let wph: wff ph
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vk: setvar k
  let vx: setvar x
  assume climliminflimsupd.1: |- ( ph -> M e. ZZ )
  assume climliminflimsupd.2: |- Z = ( ZZ>= ` M )
  assume climliminflimsupd.3: |- ( ph -> F : Z --> RR )
  assume climliminflimsupd.4: |- ( ph -> F e. dom ~~> )


  assert |- ( ph -> ( liminf ` F ) = ( limsup ` F ) )

  proof
    wph
    cF
    clsi
    cfv
    #
    cF
    clsp
    cfv
    #
    wph
    @0
    wph
    @0
    cxr
    wcel
    @0
    cxne
    #
    cr
    wcel
    @0
    cr
    wcel
    wph
    @0
    vk
    cZ
    vk
    cv
    #
    cF
    cfv
    #
    cmpt
    #
    clsi
    cfv
    #
    cxr
    wph
    cF
    @5
    clsi
    wph
    vk
    cZ
    cr
    cF
    climliminflimsupd.3
    feqmptd
    #
    fveq2d
    @6
    cxr
    wcel
    #
    wph
    @5
    cvv
    wcel
    @8
    vk
    cZ
    @4
    cZ
    cM
    cuz
    climliminflimsupd.2
    fvexi
    mptex
    @5
    cvv
    liminfcl
    ax-mp
    a1i
    eqeltrd
    wph
    @1
    cneg
    #
    @2
    cr
    wph
    vk
    cZ
    @4
    cneg
    #
    cmpt
    #
    clsp
    cfv
    #
    vk
    cZ
    @10
    cneg
    #
    cmpt
    #
    clsi
    cfv
    #
    cxne
    @9
    @2
    wph
    @10
    vk
    cM
    cZ
    wph
    vk
    nfv
    #
    climliminflimsupd.1
    climliminflimsupd.2
    wph
    @3
    cZ
    wcel
    wa
    #
    @4
    wph
    cZ
    cr
    @3
    cF
    climliminflimsupd.3
    ffvelrnda
    #
    renegcld
    #
    limsupvaluz4
    wph
    @11
    @12
    cli
    wbr
    #
    @11
    @9
    cli
    wbr
    #
    @12
    @9
    wceq
    wph
    @11
    cli
    cdm
    #
    wcel
    #
    @20
    wph
    cli
    wrel
    #
    @21
    @23
    @24
    wph
    climrel
    a1i
    wph
    @1
    vk
    cF
    cM
    cZ
    @16
    vk
    cF
    nfcv
    climliminflimsupd.2
    climliminflimsupd.1
    wph
    cF
    @22
    wcel
    cF
    @1
    cli
    wbr
    climliminflimsupd.4
    wph
    cF
    cM
    cZ
    climliminflimsupd.1
    climliminflimsupd.2
    climliminflimsupd.3
    climlimsup
    mpbid
    #
    @17
    @4
    @18
    recnd
    #
    climneg
    #
    @11
    @9
    cli
    releldm
    syl2anc
    wph
    @11
    cM
    cZ
    climliminflimsupd.1
    climliminflimsupd.2
    wph
    vk
    cZ
    @10
    cr
    @11
    @19
    @11
    eqid
    fmptd
    climlimsup
    mpbid
    @27
    @12
    @9
    @11
    climuni
    syl2anc
    wph
    @15
    @0
    wph
    @14
    cF
    clsi
    wph
    @14
    @5
    cF
    wph
    vk
    cZ
    @13
    @4
    @17
    @4
    @26
    negnegd
    mpteq2dva
    @7
    eqtr4d
    fveq2d
    xnegeqd
    3eqtr3d
    #
    wph
    @1
    wph
    @1
    vk
    cF
    cM
    cZ
    climliminflimsupd.2
    climliminflimsupd.1
    @25
    @18
    climrecl
    #
    renegcld
    eqeltrrd
    @0
    xnegrecl2
    syl2anc
    #
    recnd
    wph
    @1
    @29
    recnd
    wph
    @9
    @2
    @0
    cneg
    @28
    wph
    @0
    @30
    rexnegd
    eqtr2d
    neg11d
end
