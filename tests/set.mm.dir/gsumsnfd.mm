include "csn.mm"
include "cmpt.mm"
include "cgsu.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "cmg.mm"
include "c1.mm"
include "cv.mm"
include "wcel.mm"
include "wceq.mm"
include "elsni.mm"
include "sylan2.mm"
include "mpteq2da.mm"
include "oveq2d.mm"
include "cmnd.mm"
include "cfn.mm"
include "snfi.mm"
include "a1i.mm"
include "eqid.mm"
include "gsumconstf.mm"
include "syl3anc.mm"
include "eqtrd.mm"
include "hashsng.mm"
include "syl.mm"
include "oveq1d.mm"
include "mulg1.mm"
include "3eqtrd.mm"

theorem gsumsnfd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let cG: class G
  let cM: class M
  let cV: class V
  assume gsumsnd.b: |- B = ( Base ` G )
  assume gsumsnd.g: |- ( ph -> G e. Mnd )
  assume gsumsnd.m: |- ( ph -> M e. V )
  assume gsumsnd.c: |- ( ph -> C e. B )
  assume gsumsnd.s: |- ( ( ph /\ k = M ) -> A = C )
  assume gsumsnfd.p: |- F/ k ph
  assume gsumsnfd.c: |- F/_ k C

  disjoint M k
  assert |- ( ph -> ( G gsum ( k e. { M } |-> A ) ) = C )

  proof
    wph
    cG
    vk
    cM
    csn
    #
    cA
    cmpt
    #
    cgsu
    co
    #
    @0
    chash
    cfv
    #
    cC
    cG
    cmg
    cfv
    #
    co
    #
    c1
    cC
    @4
    co
    #
    cC
    wph
    @2
    cG
    vk
    @0
    cC
    cmpt
    #
    cgsu
    co
    #
    @5
    wph
    @1
    @7
    cG
    cgsu
    wph
    vk
    @0
    cA
    cC
    gsumsnfd.p
    vk
    cv
    #
    @0
    wcel
    wph
    @9
    cM
    wceq
    cA
    cC
    wceq
    @9
    cM
    elsni
    gsumsnd.s
    sylan2
    mpteq2da
    oveq2d
    wph
    cG
    cmnd
    wcel
    @0
    cfn
    wcel
    #
    cC
    cB
    wcel
    #
    @8
    @5
    wceq
    gsumsnd.g
    @10
    wph
    cM
    snfi
    a1i
    gsumsnd.c
    @0
    cB
    @4
    vk
    cG
    cC
    gsumsnfd.c
    gsumsnd.b
    @4
    eqid
    #
    gsumconstf
    syl3anc
    eqtrd
    wph
    @3
    c1
    cC
    @4
    wph
    cM
    cV
    wcel
    @3
    c1
    wceq
    gsumsnd.m
    cM
    cV
    hashsng
    syl
    oveq1d
    wph
    @11
    @6
    cC
    wceq
    gsumsnd.c
    cB
    @4
    cG
    cC
    gsumsnd.b
    @12
    mulg1
    syl
    3eqtrd
end
