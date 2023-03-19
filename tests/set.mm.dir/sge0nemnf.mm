include "csumge0.mm"
include "cfv.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wcel.mm"
include "cmnf.mm"
include "wne.mm"
include "sge0cl.mm"
include "xrge0neqmnf.mm"
include "syl.mm"

theorem sge0nemnf
  let wph: wff ph
  let cA: class A
  let cF: class F
  let cV: class V
  let vk: setvar k
  let vx: setvar x
  assume sge0nemnf.1: |- ( ph -> A e. V )
  assume sge0nemnf.2: |- ( ph -> F : A --> ( 0 [,] +oo ) )


  assert |- ( ph -> ( sum^ ` F ) =/= -oo )

  proof
    wph
    cF
    csumge0
    cfv
    #
    cc0
    cpnf
    cicc
    co
    wcel
    @0
    cmnf
    wne
    wph
    cF
    cV
    cA
    sge0nemnf.1
    sge0nemnf.2
    sge0cl
    @0
    xrge0neqmnf
    syl
end
