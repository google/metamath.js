include "cv.mm"
include "cfv.mm"
include "ciun.mm"
include "clsxlim.mm"
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
include "cmpt.mm"
include "cbvmpt.mm"
include "eqtri.mm"
include "meaiuninc3v.mm"
include "cbviun.mm"
include "fveq2i.mm"
include "syl6breq.mm"

theorem meaiuninc3
  let wph: wff ph
  let cS: class S
  let vn: setvar n
  let cE: class E
  let cM: class M
  let cN: class N
  let cZ: class Z
  let vk: setvar k
  let vx: setvar x
  assume meaiuninc3.p: |- F/ n ph
  assume meaiuninc3.f: |- F/_ n E
  assume meaiuninc3.m: |- ( ph -> M e. Meas )
  assume meaiuninc3.n: |- ( ph -> N e. ZZ )
  assume meaiuninc3.z: |- Z = ( ZZ>= ` N )
  assume meaiuninc3.e: |- ( ph -> E : Z --> dom M )
  assume meaiuninc3.i: |- ( ( ph /\ n e. Z ) -> ( E ` n ) C_ ( E ` ( n + 1 ) ) )
  assume meaiuninc3.s: |- S = ( n e. Z |-> ( M ` ( E ` n ) ) )

  disjoint M n
  disjoint Z n
  disjoint E k
  disjoint M k
  disjoint k n
  disjoint Z k
  disjoint k ph
  disjoint k x
  assert |- ( ph -> S ~~>* ( M ` U_ n e. Z ( E ` n ) ) )

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
    clsxlim
    wph
    cS
    vk
    cE
    cM
    cN
    cZ
    meaiuninc3.m
    meaiuninc3.n
    meaiuninc3.z
    meaiuninc3.e
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
    meaiuninc3.p
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
    meaiuninc3.f
    vn
    @0
    nfcv
    nffv
    #
    vn
    @13
    cE
    meaiuninc3.f
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
    meaiuninc3.i
    chvar
    cS
    vn
    cZ
    @4
    cM
    cfv
    #
    cmpt
    vk
    cZ
    @1
    cM
    cfv
    #
    cmpt
    meaiuninc3.s
    vn
    vk
    cZ
    @19
    @20
    vk
    @4
    cM
    vk
    cM
    nfcv
    vk
    @4
    nfcv
    #
    nffv
    vn
    @1
    cM
    vn
    cM
    nfcv
    @16
    nffv
    @17
    @4
    @1
    cM
    @18
    fveq2d
    cbvmpt
    eqtri
    meaiuninc3v
    @2
    @5
    cM
    vk
    vn
    cZ
    @1
    @4
    @16
    @21
    @0
    @3
    cE
    fveq2
    cbviun
    fveq2i
    syl6breq
end
