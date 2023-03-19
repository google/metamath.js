include "cmpt.mm"
include "caddc.mm"
include "cseq.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "eqid.mm"
include "fmptdf.mm"
include "sge0isum.mm"

theorem sge0isummpt
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cM: class M
  let cZ: class Z
  let vx: setvar x
  assume sge0isummpt.kph: |- F/ k ph
  assume sge0isummpt.a: |- ( ( ph /\ k e. Z ) -> A e. ( 0 [,) +oo ) )
  assume sge0isummpt.m: |- ( ph -> M e. ZZ )
  assume sge0isummpt.z: |- Z = ( ZZ>= ` M )
  assume sge0isummpt.b: |- ( ph -> seq M ( + , ( k e. Z |-> A ) ) ~~> B )

  disjoint Z k
  disjoint k x
  assert |- ( ph -> ( sum^ ` ( k e. Z |-> A ) ) = B )

  proof
    wph
    cB
    vk
    cZ
    cA
    cmpt
    #
    caddc
    @0
    cM
    cseq
    #
    cM
    cZ
    sge0isummpt.m
    sge0isummpt.z
    wph
    vk
    cZ
    cA
    cc0
    cpnf
    cico
    co
    @0
    sge0isummpt.kph
    sge0isummpt.a
    @0
    eqid
    fmptdf
    @1
    eqid
    sge0isummpt.b
    sge0isum
end
