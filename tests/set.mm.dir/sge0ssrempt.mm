include "cmpt.mm"
include "csumge0.mm"
include "cfv.mm"
include "cres.mm"
include "cr.mm"
include "resmptd.mm"
include "fveq2d.mm"
include "eqcomd.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "eqid.mm"
include "fmptdf.mm"
include "sge0ssre.mm"
include "eqeltrd.mm"

theorem sge0ssrempt
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let vk: setvar k
  assume sge0ssrempt.xph: |- F/ x ph
  assume sge0ssrempt.a: |- ( ph -> A e. V )
  assume sge0ssrempt.b: |- ( ( ph /\ x e. A ) -> B e. ( 0 [,] +oo ) )
  assume sge0ssrempt.re: |- ( ph -> ( sum^ ` ( x e. A |-> B ) ) e. RR )
  assume sge0ssrempt.c: |- ( ph -> C C_ A )

  disjoint A x
  disjoint C x
  disjoint k x
  assert |- ( ph -> ( sum^ ` ( x e. C |-> B ) ) e. RR )

  proof
    wph
    vx
    cC
    cB
    cmpt
    #
    csumge0
    cfv
    #
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
    #
    cr
    wph
    @4
    @1
    wph
    @3
    @0
    csumge0
    wph
    vx
    cA
    cC
    cB
    sge0ssrempt.c
    resmptd
    fveq2d
    eqcomd
    wph
    @2
    cV
    cA
    cC
    sge0ssrempt.a
    wph
    vx
    cA
    cB
    cc0
    cpnf
    cicc
    co
    @2
    sge0ssrempt.xph
    sge0ssrempt.b
    @2
    eqid
    fmptdf
    sge0ssrempt.re
    sge0ssre
    eqeltrd
end
