include "wcel.mm"
include "cfn.mm"
include "wn.mm"
include "w3a.mm"
include "chash.mm"
include "cfv.mm"
include "cpnf.mm"
include "cle.mm"
include "wbr.mm"
include "cxr.mm"
include "hashxrcl.mm"
include "pnfge.mm"
include "syl.mm"
include "3ad2ant1.mm"
include "wceq.mm"
include "hashinf.mm"
include "3adant1.mm"
include "breqtrrd.mm"

theorem nfile
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ B e. W /\ -. B e. Fin ) -> ( # ` A ) <_ ( # ` B ) )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    cB
    cfn
    wcel
    wn
    #
    w3a
    cA
    chash
    cfv
    #
    cpnf
    cB
    chash
    cfv
    #
    cle
    @0
    @1
    @3
    cpnf
    cle
    wbr
    #
    @2
    @0
    @3
    cxr
    wcel
    @5
    cA
    cV
    hashxrcl
    @3
    pnfge
    syl
    3ad2ant1
    @1
    @2
    @4
    cpnf
    wceq
    @0
    cB
    cW
    hashinf
    3adant1
    breqtrrd
end
