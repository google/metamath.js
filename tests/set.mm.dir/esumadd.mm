include "cxad.mm"
include "co.mm"
include "cesum.mm"
include "nfv.mm"
include "nfcv.mm"
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
include "eqid.mm"
include "fmptd.mm"
include "esumel.mm"
include "tsmsadd.mm"
include "eqidd.mm"
include "offval2.mm"
include "oveq2d.mm"
include "eleqtrd.mm"
include "esumid.mm"

theorem esumadd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let cV: class V
  assume esumadd.0: |- ( ph -> A e. V )
  assume esumadd.1: |- ( ( ph /\ k e. A ) -> B e. ( 0 [,] +oo ) )
  assume esumadd.2: |- ( ( ph /\ k e. A ) -> C e. ( 0 [,] +oo ) )

  disjoint A k
  disjoint V k
  disjoint k ph
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
    wph
    vk
    nfv
    #
    vk
    cA
    nfcv
    #
    esumadd.0
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
    @6
    wcel
    @0
    @6
    wcel
    esumadd.1
    esumadd.2
    cB
    cC
    ge0xaddcl
    syl2anc
    wph
    @3
    cxrs
    @6
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
    @7
    vk
    cA
    @0
    cmpt
    #
    ctsu
    co
    wph
    cA
    @6
    cxad
    @8
    @7
    @9
    cV
    @1
    @2
    xrge0base
    xrge0plusg
    @7
    ccmn
    wcel
    wph
    xrge0cmn
    a1i
    @7
    ctmd
    wcel
    wph
    xrge0tmd
    a1i
    esumadd.0
    wph
    vk
    cA
    cB
    @6
    @8
    esumadd.1
    @8
    eqid
    fmptd
    wph
    vk
    cA
    cC
    @6
    @9
    esumadd.2
    @9
    eqid
    fmptd
    wph
    cA
    cB
    vk
    cV
    @4
    @5
    esumadd.0
    esumadd.1
    esumel
    wph
    cA
    cC
    vk
    cV
    @4
    @5
    esumadd.0
    esumadd.2
    esumel
    tsmsadd
    wph
    @10
    @11
    @7
    ctsu
    wph
    vk
    cA
    cB
    cC
    cxad
    @8
    @9
    cV
    @6
    @6
    esumadd.0
    esumadd.1
    esumadd.2
    wph
    @8
    eqidd
    wph
    @9
    eqidd
    offval2
    oveq2d
    eleqtrd
    esumid
end
