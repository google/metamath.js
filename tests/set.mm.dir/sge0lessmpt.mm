include "cmpt.mm"
include "csumge0.mm"
include "cfv.mm"
include "cres.mm"
include "cle.mm"
include "wceq.mm"
include "id.mm"
include "resmptd.mm"
include "eqcomd.mm"
include "syl.mm"
include "fveq2d.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "eqid.mm"
include "fmptd.mm"
include "sge0less.mm"
include "eqbrtrd.mm"

theorem sge0lessmpt
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let vk: setvar k
  assume sge0lessmpt.a: |- ( ph -> A e. V )
  assume sge0lessmpt.b: |- ( ( ph /\ x e. A ) -> B e. ( 0 [,] +oo ) )
  assume sge0lessmpt.c: |- ( ph -> C C_ A )

  disjoint A x
  disjoint C x
  disjoint ph x
  disjoint k x
  assert |- ( ph -> ( sum^ ` ( x e. C |-> B ) ) <_ ( sum^ ` ( x e. A |-> B ) ) )

  proof
    wph
    vx
    cC
    cB
    cmpt
    #
    csumge0
    cfv
    vx
    cA
    cB
    cmpt
    #
    cC
    cres
    #
    csumge0
    cfv
    @1
    csumge0
    cfv
    cle
    wph
    @0
    @2
    csumge0
    wph
    wph
    @0
    @2
    wceq
    wph
    id
    wph
    @2
    @0
    wph
    vx
    cA
    cC
    cB
    sge0lessmpt.c
    resmptd
    eqcomd
    syl
    fveq2d
    wph
    @1
    cV
    cA
    cC
    sge0lessmpt.a
    wph
    vx
    cA
    cB
    cc0
    cpnf
    cicc
    co
    @1
    sge0lessmpt.b
    @1
    eqid
    fmptd
    sge0less
    eqbrtrd
end
