include "cmnd.mm"
include "wcel.mm"
include "cfn.mm"
include "w3a.mm"
include "cmpt.mm"
include "cgsu.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "nfcv.mm"
include "weq.mm"
include "eqidd.mm"
include "cbvmpt.mm"
include "oveq2i.mm"
include "gsumconst.mm"
include "syl5eq.mm"

theorem gsumconstf
  let cA: class A
  let cB: class B
  let c.x: class .x.
  let vk: setvar k
  let cG: class G
  let cX: class X
  let vl: setvar l
  assume gsumconstf.k: |- F/_ k X
  assume gsumconstf.b: |- B = ( Base ` G )
  assume gsumconstf.m: |- .x. = ( .g ` G )

  disjoint A k
  disjoint k l
  disjoint A l
  disjoint B l
  disjoint G l
  disjoint X l
  assert |- ( ( G e. Mnd /\ A e. Fin /\ X e. B ) -> ( G gsum ( k e. A |-> X ) ) = ( ( # ` A ) .x. X ) )

  proof
    cG
    cmnd
    wcel
    cA
    cfn
    wcel
    cX
    cB
    wcel
    w3a
    cG
    vk
    cA
    cX
    cmpt
    #
    cgsu
    co
    cG
    vl
    cA
    cX
    cmpt
    #
    cgsu
    co
    cA
    chash
    cfv
    cX
    c.x
    co
    @0
    @1
    cG
    cgsu
    vk
    vl
    cA
    cX
    cX
    vl
    cX
    nfcv
    gsumconstf.k
    vk
    vl
    weq
    cX
    eqidd
    cbvmpt
    oveq2i
    cA
    cB
    c.x
    vl
    cG
    cX
    gsumconstf.b
    gsumconstf.m
    gsumconst
    syl5eq
end
