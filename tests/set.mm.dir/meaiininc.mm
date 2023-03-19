include "cv.mm"
include "cfv.mm"
include "ciin.mm"
include "cli.mm"
include "wbr.mm"
include "cmpt.mm"
include "cdif.mm"
include "ciun.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wss.mm"
include "wi.mm"
include "nfv.mm"
include "nfan.mm"
include "nfim.mm"
include "wceq.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "sseq12d.mm"
include "imbi12d.mm"
include "chvar.mm"
include "cbvmptv.mm"
include "difeq2d.mm"
include "cbviunv.mm"
include "meaiininclem.mm"
include "eqtri.mm"
include "a1i.mm"
include "cbviinv.mm"
include "fveq2i.mm"
include "breq12d.mm"
include "mpbird.mm"

theorem meaiininc
  let wph: wff ph
  let cS: class S
  let vn: setvar n
  let cE: class E
  let cK: class K
  let cM: class M
  let cN: class N
  let cZ: class Z
  let vi: setvar i
  let vm: setvar m
  let vk: setvar k
  let vx: setvar x
  assume meaiininc.f: |- F/ n ph
  assume meaiininc.m: |- ( ph -> M e. Meas )
  assume meaiininc.n: |- ( ph -> N e. ZZ )
  assume meaiininc.z: |- Z = ( ZZ>= ` N )
  assume meaiininc.e: |- ( ph -> E : Z --> dom M )
  assume meaiininc.i: |- ( ( ph /\ n e. Z ) -> ( E ` ( n + 1 ) ) C_ ( E ` n ) )
  assume meaiininc.k: |- ( ph -> K e. ( ZZ>= ` N ) )
  assume meaiininc.r: |- ( ph -> ( M ` ( E ` K ) ) e. RR )
  assume meaiininc.s: |- S = ( n e. Z |-> ( M ` ( E ` n ) ) )

  disjoint E n
  disjoint K n
  disjoint M n
  disjoint Z n
  disjoint E i
  disjoint E m
  disjoint i m
  disjoint i n
  disjoint m n
  disjoint K i
  disjoint K m
  disjoint M i
  disjoint M m
  disjoint N i
  disjoint Z i
  disjoint Z m
  disjoint i ph
  disjoint k x
  assert |- ( ph -> S ~~> ( M ` |^|_ n e. Z ( E ` n ) ) )

  proof
    wph
    cS
    vn
    cZ
    vn
    cv
    #
    cE
    cfv
    #
    ciin
    #
    cM
    cfv
    #
    cli
    wbr
    vm
    cZ
    vm
    cv
    #
    cE
    cfv
    #
    cM
    cfv
    #
    cmpt
    #
    vi
    cZ
    vi
    cv
    #
    cE
    cfv
    #
    ciin
    #
    cM
    cfv
    #
    cli
    wbr
    wph
    @7
    vi
    cE
    vm
    cZ
    @4
    vn
    cZ
    cK
    cE
    cfv
    #
    @1
    cdif
    #
    cmpt
    #
    cfv
    #
    ciun
    @14
    cK
    cM
    cN
    cZ
    meaiininc.m
    meaiininc.n
    meaiininc.z
    meaiininc.e
    wph
    @0
    cZ
    wcel
    #
    wa
    #
    @0
    c1
    caddc
    co
    #
    cE
    cfv
    #
    @1
    wss
    #
    wi
    wph
    @8
    cZ
    wcel
    #
    wa
    #
    @8
    c1
    caddc
    co
    #
    cE
    cfv
    #
    @9
    wss
    #
    wi
    vn
    vi
    @22
    @25
    vn
    wph
    @21
    vn
    meaiininc.f
    @21
    vn
    nfv
    nfan
    @25
    vn
    nfv
    nfim
    @0
    @8
    wceq
    #
    @17
    @22
    @20
    @25
    @26
    @16
    @21
    wph
    @0
    @8
    cZ
    eleq1
    anbi2d
    @26
    @19
    @24
    @1
    @9
    @26
    @18
    @23
    cE
    @0
    @8
    c1
    caddc
    oveq1
    fveq2d
    @0
    @8
    cE
    fveq2
    #
    sseq12d
    imbi12d
    meaiininc.i
    chvar
    meaiininc.k
    meaiininc.r
    vm
    vi
    cZ
    @6
    @9
    cM
    cfv
    @4
    @8
    wceq
    @5
    @9
    cM
    @4
    @8
    cE
    fveq2
    fveq2d
    cbvmptv
    vn
    vi
    cZ
    @13
    @12
    @9
    cdif
    @26
    @1
    @9
    @12
    @27
    difeq2d
    cbvmptv
    vm
    vi
    cZ
    @15
    @8
    @14
    cfv
    @4
    @8
    @14
    fveq2
    cbviunv
    meaiininclem
    wph
    cS
    @7
    @3
    @11
    cli
    cS
    @7
    wceq
    wph
    cS
    vn
    cZ
    @1
    cM
    cfv
    #
    cmpt
    @7
    meaiininc.s
    vn
    vm
    cZ
    @28
    @6
    @0
    @4
    wceq
    @1
    @5
    cM
    @0
    @4
    cE
    fveq2
    fveq2d
    cbvmptv
    eqtri
    a1i
    @3
    @11
    wceq
    wph
    @2
    @10
    cM
    vn
    vi
    cZ
    @1
    @9
    @27
    cbviinv
    fveq2i
    a1i
    breq12d
    mpbird
end
