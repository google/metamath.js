include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "ciun.mm"
include "cli.mm"
include "wceq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "a1i.mm"
include "cfzo.mm"
include "co.mm"
include "cdif.mm"
include "eqtr3i.mm"
include "cbviunv.mm"
include "difeq2i.mm"
include "mpteq2i.mm"
include "oveq2.mm"
include "iuneq1d.mm"
include "difeq12d.mm"
include "meaiuninclem.mm"
include "eqbrtrd.mm"

theorem meaiuninc
  let wph: wff ph
  let vx: setvar x
  let cS: class S
  let vn: setvar n
  let cE: class E
  let cM: class M
  let cN: class N
  let cZ: class Z
  let vi: setvar i
  let vk: setvar k
  let vm: setvar m
  assume meaiuninc.m: |- ( ph -> M e. Meas )
  assume meaiuninc.n: |- ( ph -> N e. ZZ )
  assume meaiuninc.z: |- Z = ( ZZ>= ` N )
  assume meaiuninc.e: |- ( ph -> E : Z --> dom M )
  assume meaiuninc.i: |- ( ( ph /\ n e. Z ) -> ( E ` n ) C_ ( E ` ( n + 1 ) ) )
  assume meaiuninc.x: |- ( ph -> E. x e. RR A. n e. Z ( M ` ( E ` n ) ) <_ x )
  assume meaiuninc.s: |- S = ( n e. Z |-> ( M ` ( E ` n ) ) )

  disjoint E n
  disjoint E x
  disjoint n x
  disjoint M n
  disjoint M x
  disjoint N n
  disjoint N x
  disjoint Z n
  disjoint Z x
  disjoint n ph
  disjoint ph x
  disjoint E i
  disjoint E k
  disjoint E m
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i x
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint m n
  disjoint m x
  disjoint M i
  disjoint M m
  disjoint N i
  disjoint N k
  disjoint N m
  disjoint Z i
  disjoint Z m
  disjoint i ph
  disjoint k x
  assert |- ( ph -> S ~~> ( M ` U_ n e. Z ( E ` n ) ) )

  proof
    wph
    cS
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
    vn
    cZ
    vn
    cv
    #
    cE
    cfv
    #
    ciun
    cM
    cfv
    cli
    cS
    @3
    wceq
    wph
    cS
    vn
    cZ
    @5
    cM
    cfv
    #
    cmpt
    #
    @3
    meaiuninc.s
    vn
    vm
    cZ
    @6
    @2
    @4
    @0
    wceq
    @5
    @1
    cM
    @4
    @0
    cE
    fveq2
    fveq2d
    cbvmptv
    eqtri
    #
    a1i
    wph
    vx
    @3
    vi
    vn
    cE
    vm
    cZ
    @1
    vk
    cN
    @0
    cfzo
    co
    #
    vk
    cv
    #
    cE
    cfv
    #
    ciun
    #
    cdif
    #
    cmpt
    #
    cM
    cN
    cZ
    meaiuninc.m
    meaiuninc.n
    meaiuninc.z
    meaiuninc.e
    meaiuninc.i
    meaiuninc.x
    cS
    @3
    @7
    @8
    meaiuninc.s
    eqtr3i
    @14
    vm
    cZ
    @1
    vi
    @9
    vi
    cv
    #
    cE
    cfv
    #
    ciun
    #
    cdif
    #
    cmpt
    vn
    cZ
    @5
    vi
    cN
    @4
    cfzo
    co
    #
    @16
    ciun
    #
    cdif
    #
    cmpt
    vm
    cZ
    @13
    @18
    @12
    @17
    @1
    vk
    vi
    @9
    @11
    @16
    @10
    @15
    cE
    fveq2
    cbviunv
    difeq2i
    mpteq2i
    vm
    vn
    cZ
    @18
    @21
    @0
    @4
    wceq
    #
    @1
    @5
    @17
    @20
    @0
    @4
    cE
    fveq2
    @22
    vi
    @9
    @19
    @16
    @0
    @4
    cN
    cfzo
    oveq2
    iuneq1d
    difeq12d
    cbvmptv
    eqtri
    meaiuninclem
    eqbrtrd
end
