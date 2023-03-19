include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cvol.mm"
include "cfv.mm"
include "cprod.mm"
include "cxr.mm"
include "wcel.mm"
include "0xr.mm"
include "a1i.mm"
include "pnfxr.mm"
include "cv.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "cmin.mm"
include "cif.mm"
include "cr.mm"
include "wceq.mm"
include "volico.mm"
include "syl2anc.mm"
include "resubcld.mm"
include "0red.mm"
include "ifcld.mm"
include "eqeltrd.mm"
include "fprodreclf.mm"
include "rexrd.mm"
include "cdm.mm"
include "cle.mm"
include "icombl.mm"
include "volge0.mm"
include "syl.mm"
include "fprodge0.mm"
include "ltpnfd.mm"
include "elicod.mm"

theorem hoiprodcl3
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cX: class X
  let vx: setvar x
  assume hoiprodcl3.k: |- F/ k ph
  assume hoiprodcl3.x: |- ( ph -> X e. Fin )
  assume hoiprodcl3.a: |- ( ( ph /\ k e. X ) -> A e. RR )
  assume hoiprodcl3.b: |- ( ( ph /\ k e. X ) -> B e. RR )

  disjoint X k
  disjoint k x
  assert |- ( ph -> prod_ k e. X ( vol ` ( A [,) B ) ) e. ( 0 [,) +oo ) )

  proof
    wph
    cc0
    cpnf
    cX
    cA
    cB
    cico
    co
    #
    cvol
    cfv
    #
    vk
    cprod
    #
    cc0
    cxr
    wcel
    wph
    0xr
    a1i
    cpnf
    cxr
    wcel
    wph
    pnfxr
    a1i
    wph
    @2
    wph
    cX
    @1
    vk
    hoiprodcl3.k
    hoiprodcl3.x
    wph
    vk
    cv
    cX
    wcel
    wa
    #
    @1
    cA
    cB
    clt
    wbr
    #
    cB
    cA
    cmin
    co
    #
    cc0
    cif
    #
    cr
    @3
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    @1
    @6
    wceq
    hoiprodcl3.a
    hoiprodcl3.b
    cA
    cB
    volico
    syl2anc
    @3
    @4
    @5
    cc0
    cr
    @3
    cB
    cA
    hoiprodcl3.b
    hoiprodcl3.a
    resubcld
    @3
    0red
    ifcld
    eqeltrd
    #
    fprodreclf
    #
    rexrd
    wph
    cX
    @1
    vk
    hoiprodcl3.k
    hoiprodcl3.x
    @8
    @3
    @0
    cvol
    cdm
    wcel
    #
    cc0
    @1
    cle
    wbr
    @3
    @7
    cB
    cxr
    wcel
    @10
    hoiprodcl3.a
    @3
    cB
    hoiprodcl3.b
    rexrd
    cA
    cB
    icombl
    syl2anc
    @0
    volge0
    syl
    fprodge0
    wph
    @2
    @9
    ltpnfd
    elicod
end
