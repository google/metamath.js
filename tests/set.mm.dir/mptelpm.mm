include "cmpt.mm"
include "cpm.mm"
include "co.mm"
include "wcel.mm"
include "cdm.mm"
include "wf.mm"
include "wss.mm"
include "wa.mm"
include "eqid.mm"
include "fmptd.mm"
include "dmmptd.mm"
include "eqcomd.mm"
include "feq2d.mm"
include "mpbid.mm"
include "eqsstrd.mm"
include "jca.mm"
include "wb.mm"
include "elpm2g.mm"
include "syl2anc.mm"
include "mpbird.mm"

theorem mptelpm
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cV: class V
  let cW: class W
  assume mptelpm.b: |- ( ( ph /\ x e. A ) -> B e. C )
  assume mptelpm.a: |- ( ph -> A C_ D )
  assume mptelpm.c: |- ( ph -> C e. V )
  assume mptelpm.d: |- ( ph -> D e. W )

  disjoint A x
  disjoint C x
  disjoint ph x
  assert |- ( ph -> ( x e. A |-> B ) e. ( C ^pm D ) )

  proof
    wph
    vx
    cA
    cB
    cmpt
    #
    cC
    cD
    cpm
    co
    wcel
    #
    @0
    cdm
    #
    cC
    @0
    wf
    #
    @2
    cD
    wss
    #
    wa
    #
    wph
    @3
    @4
    wph
    cA
    cC
    @0
    wf
    @3
    wph
    vx
    cA
    cB
    cC
    @0
    mptelpm.b
    @0
    eqid
    #
    fmptd
    wph
    cA
    @2
    cC
    @0
    wph
    @2
    cA
    wph
    vx
    @0
    cA
    cB
    cC
    @6
    mptelpm.b
    dmmptd
    #
    eqcomd
    feq2d
    mpbid
    wph
    @2
    cA
    cD
    @7
    mptelpm.a
    eqsstrd
    jca
    wph
    cC
    cV
    wcel
    cD
    cW
    wcel
    @1
    @5
    wb
    mptelpm.c
    mptelpm.d
    cC
    cD
    @0
    cV
    cW
    elpm2g
    syl2anc
    mpbird
end
