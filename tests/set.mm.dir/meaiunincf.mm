include "cv.mm"
include "cfv.mm"
include "ciun.mm"
include "cli.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wss.mm"
include "wi.mm"
include "nfv.mm"
include "nfan.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfss.mm"
include "nfim.mm"
include "wceq.mm"
include "eleq1w.mm"
include "anbi2d.mm"
include "fveq2.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "sseq12d.mm"
include "imbi12d.mm"
include "chvar.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "breq2.mm"
include "ralbidv.mm"
include "wb.mm"
include "nfbr.mm"
include "breq1d.mm"
include "cbvral.mm"
include "a1i.mm"
include "bitrd.mm"
include "cbvrex.mm"
include "sylib.mm"
include "cmpt.mm"
include "cbvmpt.mm"
include "eqtri.mm"
include "meaiuninc.mm"
include "cbviun.mm"
include "fveq2i.mm"
include "syl6breq.mm"

theorem meaiunincf
  let wph: wff ph
  let vx: setvar x
  let cS: class S
  let vn: setvar n
  let cE: class E
  let cM: class M
  let cN: class N
  let cZ: class Z
  let vk: setvar k
  let vy: setvar y
  assume meaiunincf.p: |- F/ n ph
  assume meaiunincf.f: |- F/_ n E
  assume meaiunincf.m: |- ( ph -> M e. Meas )
  assume meaiunincf.n: |- ( ph -> N e. ZZ )
  assume meaiunincf.z: |- Z = ( ZZ>= ` N )
  assume meaiunincf.e: |- ( ph -> E : Z --> dom M )
  assume meaiunincf.i: |- ( ( ph /\ n e. Z ) -> ( E ` n ) C_ ( E ` ( n + 1 ) ) )
  assume meaiunincf.x: |- ( ph -> E. x e. RR A. n e. Z ( M ` ( E ` n ) ) <_ x )
  assume meaiunincf.s: |- S = ( n e. Z |-> ( M ` ( E ` n ) ) )

  disjoint E x
  disjoint M n
  disjoint M x
  disjoint n x
  disjoint Z n
  disjoint Z x
  disjoint E k
  disjoint E y
  disjoint k x
  disjoint k y
  disjoint x y
  disjoint M k
  disjoint M y
  disjoint k n
  disjoint n y
  disjoint N k
  disjoint N y
  disjoint Z k
  disjoint Z y
  disjoint k ph
  disjoint ph y
  disjoint k x
  assert |- ( ph -> S ~~> ( M ` U_ n e. Z ( E ` n ) ) )

  proof
    wph
    cS
    vk
    cZ
    vk
    cv
    #
    cE
    cfv
    #
    ciun
    #
    cM
    cfv
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
    cM
    cfv
    cli
    wph
    vy
    cS
    vk
    cE
    cM
    cN
    cZ
    meaiunincf.m
    meaiunincf.n
    meaiunincf.z
    meaiunincf.e
    wph
    @3
    cZ
    wcel
    #
    wa
    #
    @4
    @3
    c1
    caddc
    co
    #
    cE
    cfv
    #
    wss
    #
    wi
    wph
    @0
    cZ
    wcel
    #
    wa
    #
    @1
    @0
    c1
    caddc
    co
    #
    cE
    cfv
    #
    wss
    #
    wi
    vn
    vk
    @12
    @15
    vn
    wph
    @11
    vn
    meaiunincf.p
    @11
    vn
    nfv
    nfan
    vn
    @1
    @14
    vn
    @0
    cE
    meaiunincf.f
    vn
    @0
    nfcv
    nffv
    #
    vn
    @13
    cE
    meaiunincf.f
    vn
    @13
    nfcv
    nffv
    nfss
    nfim
    @3
    @0
    wceq
    #
    @7
    @12
    @10
    @15
    @17
    @6
    @11
    wph
    vn
    vk
    cZ
    eleq1w
    anbi2d
    @17
    @4
    @1
    @9
    @14
    @3
    @0
    cE
    fveq2
    #
    @17
    @8
    @13
    cE
    @3
    @0
    c1
    caddc
    oveq1
    fveq2d
    sseq12d
    imbi12d
    meaiunincf.i
    chvar
    wph
    @4
    cM
    cfv
    #
    vx
    cv
    #
    cle
    wbr
    #
    vn
    cZ
    wral
    #
    vx
    cr
    wrex
    @1
    cM
    cfv
    #
    vy
    cv
    #
    cle
    wbr
    #
    vk
    cZ
    wral
    #
    vy
    cr
    wrex
    meaiunincf.x
    @22
    @26
    vx
    vy
    cr
    @22
    vy
    nfv
    @26
    vx
    nfv
    @20
    @24
    wceq
    #
    @22
    @19
    @24
    cle
    wbr
    #
    vn
    cZ
    wral
    #
    @26
    @27
    @21
    @28
    vn
    cZ
    @20
    @24
    @19
    cle
    breq2
    ralbidv
    @29
    @26
    wb
    @27
    @28
    @25
    vn
    vk
    cZ
    @28
    vk
    nfv
    vn
    @23
    @24
    cle
    vn
    @1
    cM
    vn
    cM
    nfcv
    @16
    nffv
    #
    vn
    cle
    nfcv
    vn
    @24
    nfcv
    nfbr
    @17
    @19
    @23
    @24
    cle
    @17
    @4
    @1
    cM
    @18
    fveq2d
    #
    breq1d
    cbvral
    a1i
    bitrd
    cbvrex
    sylib
    cS
    vn
    cZ
    @19
    cmpt
    vk
    cZ
    @23
    cmpt
    meaiunincf.s
    vn
    vk
    cZ
    @19
    @23
    vk
    @19
    nfcv
    @30
    @31
    cbvmpt
    eqtri
    meaiuninc
    @2
    @5
    cM
    vk
    vn
    cZ
    @1
    @4
    @16
    vk
    @4
    nfcv
    @0
    @3
    cE
    fveq2
    cbviun
    fveq2i
    syl6breq
end
