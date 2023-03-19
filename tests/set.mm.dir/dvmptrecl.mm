include "cr.mm"
include "wcel.mm"
include "cmpt.mm"
include "wf.mm"
include "wral.mm"
include "cdv.mm"
include "co.mm"
include "cdm.mm"
include "wss.mm"
include "eqid.mm"
include "fmptd.mm"
include "dvfre.mm"
include "syl2anc.mm"
include "dmeqd.mm"
include "wceq.mm"
include "ralrimiva.mm"
include "dmmptg.mm"
include "syl.mm"
include "eqtrd.mm"
include "feq12d.mm"
include "mpbid.mm"
include "fmpt.mm"
include "sylibr.mm"
include "r19.21bi.mm"

theorem dvmptrecl
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cS: class S
  let cV: class V
  assume dvmptrecl.s: |- ( ph -> S C_ RR )
  assume dvmptrecl.a: |- ( ( ph /\ x e. S ) -> A e. RR )
  assume dvmptrecl.v: |- ( ( ph /\ x e. S ) -> B e. V )
  assume dvmptrecl.b: |- ( ph -> ( RR _D ( x e. S |-> A ) ) = ( x e. S |-> B ) )

  disjoint ph x
  disjoint S x
  assert |- ( ( ph /\ x e. S ) -> B e. RR )

  proof
    wph
    cB
    cr
    wcel
    #
    vx
    cS
    wph
    cS
    cr
    vx
    cS
    cB
    cmpt
    #
    wf
    #
    @0
    vx
    cS
    wral
    wph
    cr
    vx
    cS
    cA
    cmpt
    #
    cdv
    co
    #
    cdm
    #
    cr
    @4
    wf
    #
    @2
    wph
    cS
    cr
    @3
    wf
    cS
    cr
    wss
    @6
    wph
    vx
    cS
    cA
    cr
    @3
    dvmptrecl.a
    @3
    eqid
    fmptd
    dvmptrecl.s
    cS
    @3
    dvfre
    syl2anc
    wph
    @5
    cS
    cr
    @4
    @1
    dvmptrecl.b
    wph
    @5
    @1
    cdm
    #
    cS
    wph
    @4
    @1
    dvmptrecl.b
    dmeqd
    wph
    cB
    cV
    wcel
    #
    vx
    cS
    wral
    @7
    cS
    wceq
    wph
    @8
    vx
    cS
    dvmptrecl.v
    ralrimiva
    vx
    cS
    cB
    cV
    dmmptg
    syl
    eqtrd
    feq12d
    mpbid
    vx
    cS
    cr
    cB
    @1
    @1
    eqid
    fmpt
    sylibr
    r19.21bi
end
