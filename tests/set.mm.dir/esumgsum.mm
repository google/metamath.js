include "cxrs.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "cress.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cfn.mm"
include "xrge0base.mm"
include "xrge00.mm"
include "ccmn.mm"
include "wcel.mm"
include "xrge0cmn.mm"
include "a1i.mm"
include "ctps.mm"
include "xrge0tps.mm"
include "nfcv.mm"
include "eqid.mm"
include "fmptdF.mm"
include "cxr.mm"
include "wral.mm"
include "wfn.mm"
include "cv.mm"
include "ex.mm"
include "ralrimi.mm"
include "fnmptf.mm"
include "syl.mm"
include "0xr.mm"
include "fndmfifsupp.mm"
include "tsmsid.mm"
include "esumid.mm"

theorem esumgsum
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  assume esumgsum.1: |- F/ k ph
  assume esumgsum.2: |- F/_ k A
  assume esumgsum.3: |- ( ph -> A e. Fin )
  assume esumgsum.4: |- ( ( ph /\ k e. A ) -> B e. ( 0 [,] +oo ) )


  assert |- ( ph -> sum* k e. A B = ( ( RR*s |`s ( 0 [,] +oo ) ) gsum ( k e. A |-> B ) ) )

  proof
    wph
    cA
    cB
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
    cgsu
    co
    vk
    cfn
    esumgsum.1
    esumgsum.2
    esumgsum.3
    esumgsum.4
    wph
    cA
    @0
    @2
    @1
    cfn
    cc0
    xrge0base
    xrge00
    @1
    ccmn
    wcel
    wph
    xrge0cmn
    a1i
    @1
    ctps
    wcel
    wph
    xrge0tps
    a1i
    esumgsum.3
    wph
    vk
    cA
    cB
    @0
    @2
    esumgsum.1
    esumgsum.2
    vk
    @0
    nfcv
    esumgsum.4
    @2
    eqid
    fmptdF
    wph
    cA
    @2
    cxr
    cc0
    wph
    cB
    @0
    wcel
    #
    vk
    cA
    wral
    @2
    cA
    wfn
    wph
    @3
    vk
    cA
    esumgsum.1
    wph
    vk
    cv
    cA
    wcel
    @3
    esumgsum.4
    ex
    ralrimi
    vk
    cA
    cB
    @0
    esumgsum.2
    fnmptf
    syl
    esumgsum.3
    cc0
    cxr
    wcel
    wph
    0xr
    a1i
    fndmfifsupp
    tsmsid
    esumid
end
