include "cxrs.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "cress.mm"
include "cmpt.mm"
include "ctsu.mm"
include "cuni.mm"
include "cesum.mm"
include "eqid.mm"
include "nfcv.mm"
include "fmptdF.mm"
include "xrge0tsmseq.mm"
include "df-esum.mm"
include "syl6reqr.mm"

theorem esumid
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let cV: class V
  assume esumid.p: |- F/ k ph
  assume esumid.0: |- F/_ k A
  assume esumid.1: |- ( ph -> A e. V )
  assume esumid.2: |- ( ( ph /\ k e. A ) -> B e. ( 0 [,] +oo ) )
  assume esumid.3: |- ( ph -> C e. ( ( RR*s |`s ( 0 [,] +oo ) ) tsums ( k e. A |-> B ) ) )


  assert |- ( ph -> sum* k e. A B = C )

  proof
    wph
    cC
    cxrs
    cc0
    cpnf
    cicc
    co
    #
    cress
    co
    #
    vk
    cA
    cB
    cmpt
    #
    ctsu
    co
    cuni
    cA
    cB
    vk
    cesum
    wph
    cA
    cC
    @2
    @1
    cV
    @1
    eqid
    esumid.1
    wph
    vk
    cA
    cB
    @0
    @2
    esumid.p
    esumid.0
    vk
    @0
    nfcv
    esumid.2
    @2
    eqid
    fmptdF
    esumid.3
    xrge0tsmseq
    cA
    cB
    vk
    df-esum
    syl6reqr
end
