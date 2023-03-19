include "cspthson.mm"
include "cfv.mm"
include "co.mm"
include "wbr.mm"
include "cvtx.mm"
include "wcel.mm"
include "wa.mm"
include "cvv.mm"
include "ctrlson.mm"
include "cspths.mm"
include "w3a.mm"
include "cpthson.mm"
include "eqid.mm"
include "spthonprop.mm"
include "3simpc.mm"
include "3anim1i.mm"
include "syl.mm"
include "cpths.mm"
include "spthispth.mm"
include "anim2i.mm"
include "3ad2ant3.mm"
include "wb.mm"
include "ispthson.mm"
include "3adant3.mm"
include "mpbird.mm"

theorem spthonpthon
  let cA: class A
  let cB: class B
  let cP: class P
  let cF: class F
  let cG: class G


  assert |- ( F ( A ( SPathsOn ` G ) B ) P -> F ( A ( PathsOn ` G ) B ) P )

  proof
    cF
    cP
    cA
    cB
    cG
    cspthson
    cfv
    co
    wbr
    #
    cA
    cG
    cvtx
    cfv
    #
    wcel
    #
    cB
    @1
    wcel
    #
    wa
    #
    cF
    cvv
    wcel
    cP
    cvv
    wcel
    wa
    #
    cF
    cP
    cA
    cB
    cG
    ctrlson
    cfv
    co
    wbr
    #
    cF
    cP
    cG
    cspths
    cfv
    wbr
    #
    wa
    #
    w3a
    #
    cF
    cP
    cA
    cB
    cG
    cpthson
    cfv
    co
    wbr
    #
    @0
    cG
    cvv
    wcel
    #
    @2
    @3
    w3a
    #
    @5
    @8
    w3a
    @9
    cA
    cB
    cP
    cF
    cG
    @1
    @1
    eqid
    #
    spthonprop
    @12
    @4
    @5
    @8
    @11
    @2
    @3
    3simpc
    3anim1i
    syl
    @9
    @10
    @6
    cF
    cP
    cG
    cpths
    cfv
    wbr
    #
    wa
    #
    @8
    @4
    @15
    @5
    @7
    @14
    @6
    cP
    cF
    cG
    spthispth
    anim2i
    3ad2ant3
    @4
    @5
    @10
    @15
    wb
    @8
    cA
    cB
    cP
    cvv
    cF
    cG
    @1
    cvv
    @13
    ispthson
    3adant3
    mpbird
    syl
end
