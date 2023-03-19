include "cmpt.mm"
include "clo1.mm"
include "wcel.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cfv.mm"
include "wi.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "wf.mm"
include "wss.mm"
include "wb.mm"
include "eqid.mm"
include "fmptd.mm"
include "ello12.mm"
include "syl2anc.mm"
include "nfv.mm"
include "nffvmpt1.mm"
include "nfcv.mm"
include "nfbr.mm"
include "nfim.mm"
include "wceq.mm"
include "breq2.mm"
include "fveq2.mm"
include "breq1d.mm"
include "imbi12d.mm"
include "cbvral.mm"
include "wa.mm"
include "simpr.mm"
include "fvmpt2.mm"
include "imbi2d.mm"
include "ralbidva.mm"
include "syl5bb.mm"
include "2rexbidv.mm"
include "bitrd.mm"

theorem ello1mpt
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vm: setvar m
  let vz: setvar z
  let cC: class C
  let cM: class M
  assume ello1mpt.1: |- ( ph -> A C_ RR )
  assume ello1mpt.2: |- ( ( ph /\ x e. A ) -> B e. RR )

  disjoint m x
  disjoint m y
  disjoint A m
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B m
  disjoint B y
  disjoint m ph
  disjoint ph x
  disjoint ph y
  disjoint m z
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint C m
  disjoint C x
  disjoint C y
  disjoint M m
  disjoint M x
  assert |- ( ph -> ( ( x e. A |-> B ) e. <_O(1) <-> E. y e. RR E. m e. RR A. x e. A ( y <_ x -> B <_ m ) ) )

  proof
    wph
    vx
    cA
    cB
    cmpt
    #
    clo1
    wcel
    #
    vy
    cv
    #
    vz
    cv
    #
    cle
    wbr
    #
    @3
    @0
    cfv
    #
    vm
    cv
    #
    cle
    wbr
    #
    wi
    #
    vz
    cA
    wral
    #
    vm
    cr
    wrex
    vy
    cr
    wrex
    #
    @2
    vx
    cv
    #
    cle
    wbr
    #
    cB
    @6
    cle
    wbr
    #
    wi
    #
    vx
    cA
    wral
    #
    vm
    cr
    wrex
    vy
    cr
    wrex
    wph
    cA
    cr
    @0
    wf
    cA
    cr
    wss
    @1
    @10
    wb
    wph
    vx
    cA
    cB
    cr
    @0
    ello1mpt.2
    @0
    eqid
    #
    fmptd
    ello1mpt.1
    vy
    vz
    cA
    vm
    @0
    ello12
    syl2anc
    wph
    @9
    @15
    vy
    vm
    cr
    cr
    @9
    @12
    @11
    @0
    cfv
    #
    @6
    cle
    wbr
    #
    wi
    #
    vx
    cA
    wral
    wph
    @15
    @8
    @19
    vz
    vx
    cA
    @4
    @7
    vx
    @4
    vx
    nfv
    vx
    @5
    @6
    cle
    vx
    cA
    cB
    @3
    nffvmpt1
    vx
    cle
    nfcv
    vx
    @6
    nfcv
    nfbr
    nfim
    @19
    vz
    nfv
    @3
    @11
    wceq
    #
    @4
    @12
    @7
    @18
    @3
    @11
    @2
    cle
    breq2
    @20
    @5
    @17
    @6
    cle
    @3
    @11
    @0
    fveq2
    breq1d
    imbi12d
    cbvral
    wph
    @19
    @14
    vx
    cA
    wph
    @11
    cA
    wcel
    #
    wa
    #
    @18
    @13
    @12
    @22
    @17
    cB
    @6
    cle
    @22
    @21
    cB
    cr
    wcel
    @17
    cB
    wceq
    wph
    @21
    simpr
    ello1mpt.2
    vx
    cA
    cB
    cr
    @0
    @16
    fvmpt2
    syl2anc
    breq1d
    imbi2d
    ralbidva
    syl5bb
    2rexbidv
    bitrd
end
