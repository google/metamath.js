include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "ccn.mm"
include "co.mm"
include "cc.mm"
include "ccncf.mm"
include "cv.mm"
include "cmin.mm"
include "cprod.mm"
include "cmpt.mm"
include "wceq.mm"
include "a1i.mm"
include "eqid.mm"
include "ctopon.mm"
include "wcel.mm"
include "cnfldtopon.mm"
include "wa.mm"
include "sub2cncfd.mm"
include "cncfcn1.mm"
include "eleqtrd.mm"
include "fprodcn.mm"
include "eqeltrd.mm"
include "eqcomd.mm"

theorem fprodsub2cncf
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cF: class F
  assume fprodsub2cncf.k: |- F/ k ph
  assume fprodsub2cncf.a: |- ( ph -> A e. Fin )
  assume fprodsub2cncf.b: |- ( ( ph /\ k e. A ) -> B e. CC )
  assume fprodsub2cncf.f: |- F = ( x e. CC |-> prod_ k e. A ( B - x ) )

  disjoint A k
  disjoint A x
  disjoint k x
  disjoint B x
  disjoint ph x
  disjoint k x
  assert |- ( ph -> F e. ( CC -cn-> CC ) )

  proof
    wph
    cF
    ccnfld
    ctopn
    cfv
    #
    @0
    ccn
    co
    #
    cc
    cc
    ccncf
    co
    #
    wph
    cF
    vx
    cc
    cA
    cB
    vx
    cv
    cmin
    co
    #
    vk
    cprod
    cmpt
    #
    @1
    cF
    @4
    wceq
    wph
    fprodsub2cncf.f
    a1i
    wph
    vx
    cA
    @3
    vk
    @0
    @0
    cc
    fprodsub2cncf.k
    @0
    eqid
    #
    @0
    cc
    ctopon
    cfv
    wcel
    wph
    @0
    @5
    cnfldtopon
    a1i
    fprodsub2cncf.a
    wph
    vk
    cv
    cA
    wcel
    wa
    #
    vx
    cc
    @3
    cmpt
    #
    @2
    @1
    @6
    vx
    cB
    @7
    fprodsub2cncf.b
    @7
    eqid
    sub2cncfd
    @2
    @1
    wceq
    #
    @6
    @0
    @5
    cncfcn1
    #
    a1i
    eleqtrd
    fprodcn
    eqeltrd
    wph
    @2
    @1
    @8
    wph
    @9
    a1i
    eqcomd
    eleqtrd
end
