include "cxad.mm"
include "co.mm"
include "cesum.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "ge0xaddcl.mm"
include "syl2anc.mm"
include "cxrs.mm"
include "cress.mm"
include "cmpt.mm"
include "cof.mm"
include "ctsu.mm"
include "xrge0base.mm"
include "xrge0plusg.mm"
include "ccmn.mm"
include "xrge0cmn.mm"
include "a1i.mm"
include "ctmd.mm"
include "xrge0tmd.mm"
include "nfcv.mm"
include "eqid.mm"
include "fmptdF.mm"
include "esumel.mm"
include "tsmsadd.mm"
include "eqidd.mm"
include "offval2f.mm"
include "oveq2d.mm"
include "eleqtrd.mm"
include "esumid.mm"

theorem esumaddf
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let cV: class V
  assume esumaddf.0: |- F/ k ph
  assume esumaddf.a: |- F/_ k A
  assume esumaddf.1: |- ( ph -> A e. V )
  assume esumaddf.2: |- ( ( ph /\ k e. A ) -> B e. ( 0 [,] +oo ) )
  assume esumaddf.3: |- ( ( ph /\ k e. A ) -> C e. ( 0 [,] +oo ) )

  disjoint V k
  assert |- ( ph -> sum* k e. A ( B +e C ) = ( sum* k e. A B +e sum* k e. A C ) )

  proof
    wph
    cA
    cB
    cC
    cxad
    co
    #
    cA
    cB
    vk
    cesum
    #
    cA
    cC
    vk
    cesum
    #
    cxad
    co
    #
    vk
    cV
    esumaddf.0
    esumaddf.a
    esumaddf.1
    wph
    vk
    cv
    cA
    wcel
    wa
    cB
    cc0
    cpnf
    cicc
    co
    #
    wcel
    cC
    @4
    wcel
    @0
    @4
    wcel
    esumaddf.2
    esumaddf.3
    cB
    cC
    ge0xaddcl
    syl2anc
    wph
    @3
    cxrs
    @4
    cress
    co
    #
    vk
    cA
    cB
    cmpt
    #
    vk
    cA
    cC
    cmpt
    #
    cxad
    cof
    co
    #
    ctsu
    co
    @5
    vk
    cA
    @0
    cmpt
    #
    ctsu
    co
    wph
    cA
    @4
    cxad
    @6
    @5
    @7
    cV
    @1
    @2
    xrge0base
    xrge0plusg
    @5
    ccmn
    wcel
    wph
    xrge0cmn
    a1i
    @5
    ctmd
    wcel
    wph
    xrge0tmd
    a1i
    esumaddf.1
    wph
    vk
    cA
    cB
    @4
    @6
    esumaddf.0
    esumaddf.a
    vk
    @4
    nfcv
    #
    esumaddf.2
    @6
    eqid
    fmptdF
    wph
    vk
    cA
    cC
    @4
    @7
    esumaddf.0
    esumaddf.a
    @10
    esumaddf.3
    @7
    eqid
    fmptdF
    wph
    cA
    cB
    vk
    cV
    esumaddf.0
    esumaddf.a
    esumaddf.1
    esumaddf.2
    esumel
    wph
    cA
    cC
    vk
    cV
    esumaddf.0
    esumaddf.a
    esumaddf.1
    esumaddf.3
    esumel
    tsmsadd
    wph
    @8
    @9
    @5
    ctsu
    wph
    vk
    cA
    cB
    cC
    cxad
    @6
    @7
    cV
    @4
    @4
    esumaddf.0
    esumaddf.a
    esumaddf.1
    esumaddf.2
    esumaddf.3
    wph
    @6
    eqidd
    wph
    @7
    eqidd
    offval2f
    oveq2d
    eleqtrd
    esumid
end
