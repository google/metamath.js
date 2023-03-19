include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cvv.mm"
include "wcel.mm"
include "cuz.mm"
include "clsp.mm"
include "cli.mm"
include "wbr.mm"
include "cdm.mm"
include "fvexi.mm"
include "a1i.mm"
include "mptexd.mm"
include "fvexd.mm"
include "smflimsuplem5.mm"
include "cz.mm"
include "eluzelz2.mm"
include "syl.mm"
include "eqid.mm"
include "wss.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "uzss.mm"
include "syl6sseqr.mm"
include "ssid.mm"
include "wa.mm"
include "climeqmpt.mm"
include "mpbird.mm"
include "breldmg.mm"
include "syl3anc.mm"

theorem smflimsuplem6
  let wph: wff ph
  let vx: setvar x
  let cS: class S
  let vm: setvar m
  let vn: setvar n
  let cE: class E
  let cF: class F
  let cH: class H
  let cM: class M
  let cN: class N
  let cX: class X
  let cZ: class Z
  let vk: setvar k
  assume smflimsuplem6.a: |- F/ n ph
  assume smflimsuplem6.b: |- F/ m ph
  assume smflimsuplem6.m: |- ( ph -> M e. ZZ )
  assume smflimsuplem6.z: |- Z = ( ZZ>= ` M )
  assume smflimsuplem6.s: |- ( ph -> S e. SAlg )
  assume smflimsuplem6.f: |- ( ph -> F : Z --> ( SMblFn ` S ) )
  assume smflimsuplem6.e: |- E = ( n e. Z |-> { x e. |^|_ m e. ( ZZ>= ` n ) dom ( F ` m ) | sup ( ran ( m e. ( ZZ>= ` n ) |-> ( ( F ` m ) ` x ) ) , RR* , < ) e. RR } )
  assume smflimsuplem6.h: |- H = ( n e. Z |-> ( x e. ( E ` n ) |-> sup ( ran ( m e. ( ZZ>= ` n ) |-> ( ( F ` m ) ` x ) ) , RR* , < ) ) )
  assume smflimsuplem6.r: |- ( ph -> ( limsup ` ( m e. Z |-> ( ( F ` m ) ` X ) ) ) e. RR )
  assume smflimsuplem6.n: |- ( ph -> N e. Z )
  assume smflimsuplem6.x: |- ( ph -> X e. |^|_ m e. ( ZZ>= ` N ) dom ( F ` m ) )

  disjoint F n
  disjoint F x
  disjoint n x
  disjoint M m
  disjoint N m
  disjoint N n
  disjoint m n
  disjoint X m
  disjoint X n
  disjoint Z m
  disjoint Z n
  disjoint Z x
  disjoint m x
  disjoint k x
  assert |- ( ph -> ( n e. Z |-> ( ( H ` n ) ` X ) ) e. dom ~~> )

  proof
    wph
    vn
    cZ
    cX
    vn
    cv
    #
    cH
    cfv
    #
    cfv
    #
    cmpt
    #
    cvv
    wcel
    vm
    cN
    cuz
    cfv
    #
    cX
    vm
    cv
    cF
    cfv
    cfv
    cmpt
    #
    clsp
    cfv
    #
    cvv
    wcel
    @3
    @6
    cli
    wbr
    #
    @3
    cli
    cdm
    wcel
    wph
    vn
    cZ
    @2
    cvv
    cZ
    cvv
    wcel
    wph
    cZ
    cM
    cuz
    smflimsuplem6.z
    fvexi
    a1i
    #
    mptexd
    wph
    @5
    clsp
    fvexd
    wph
    @7
    vn
    @4
    @2
    cmpt
    @6
    cli
    wbr
    wph
    vx
    cS
    vm
    vn
    cE
    cF
    cH
    cM
    cN
    cX
    cZ
    smflimsuplem6.a
    smflimsuplem6.b
    smflimsuplem6.m
    smflimsuplem6.z
    smflimsuplem6.s
    smflimsuplem6.f
    smflimsuplem6.e
    smflimsuplem6.h
    smflimsuplem6.r
    smflimsuplem6.n
    smflimsuplem6.x
    smflimsuplem5
    wph
    vn
    cZ
    @4
    @2
    @6
    cvv
    cN
    cvv
    cvv
    @4
    smflimsuplem6.a
    @8
    wph
    cN
    cuz
    fvexd
    wph
    cN
    cZ
    wcel
    #
    cN
    cz
    wcel
    smflimsuplem6.n
    cM
    cN
    cZ
    smflimsuplem6.z
    eluzelz2
    syl
    @4
    eqid
    wph
    @9
    @4
    cZ
    wss
    smflimsuplem6.n
    @9
    @4
    cM
    cuz
    cfv
    #
    cZ
    @9
    cN
    @10
    wcel
    #
    @4
    @10
    wss
    @9
    @11
    cZ
    @10
    cN
    smflimsuplem6.z
    eleq2i
    biimpi
    cM
    cN
    uzss
    syl
    smflimsuplem6.z
    syl6sseqr
    syl
    @4
    @4
    wss
    wph
    @4
    ssid
    a1i
    wph
    @0
    @4
    wcel
    wa
    cX
    @1
    fvexd
    climeqmpt
    mpbird
    @3
    @6
    cvv
    cvv
    cli
    breldmg
    syl3anc
end
