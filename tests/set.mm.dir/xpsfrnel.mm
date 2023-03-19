include "c2o.mm"
include "cv.mm"
include "c0.mm"
include "wceq.mm"
include "cif.mm"
include "cixp.mm"
include "wcel.mm"
include "cvv.mm"
include "wfn.mm"
include "cfv.mm"
include "wral.mm"
include "w3a.mm"
include "c1o.mm"
include "elixp2.mm"
include "3ancoma.mm"
include "wa.mm"
include "cpr.mm"
include "df2o3.mm"
include "raleqi.mm"
include "0ex.mm"
include "con0.mm"
include "1on.mm"
include "elexi.mm"
include "fveq2.mm"
include "iftrue.mm"
include "eleq12d.mm"
include "wne.mm"
include "1n0.mm"
include "neeq1.mm"
include "mpbiri.mm"
include "ifnefalse.mm"
include "syl.mm"
include "ralpr.mm"
include "bitri.mm"
include "cfn.mm"
include "com.mm"
include "2onn.mm"
include "nnfi.mm"
include "ax-mp.mm"
include "fnfi.mm"
include "mpan2.mm"
include "elex.mm"
include "biantrurd.mm"
include "syl5rbbr.mm"
include "pm5.32i.mm"
include "3anass.mm"
include "3bitr4i.mm"

theorem xpsfrnel
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cG: class G
  let cX: class X
  let cY: class Y

  disjoint A k
  disjoint B k
  disjoint G k
  disjoint X k
  disjoint Y k
  assert |- ( G e. X_ k e. 2o if ( k = (/) , A , B ) <-> ( G Fn 2o /\ ( G ` (/) ) e. A /\ ( G ` 1o ) e. B ) )

  proof
    cG
    vk
    c2o
    vk
    cv
    #
    c0
    wceq
    #
    cA
    cB
    cif
    #
    cixp
    wcel
    cG
    cvv
    wcel
    #
    cG
    c2o
    wfn
    #
    @0
    cG
    cfv
    #
    @2
    wcel
    #
    vk
    c2o
    wral
    #
    w3a
    #
    @4
    c0
    cG
    cfv
    #
    cA
    wcel
    #
    c1o
    cG
    cfv
    #
    cB
    wcel
    #
    w3a
    #
    vk
    c2o
    @2
    cG
    elixp2
    @8
    @4
    @3
    @7
    w3a
    #
    @13
    @3
    @4
    @7
    3ancoma
    @4
    @3
    @7
    wa
    #
    wa
    @4
    @10
    @12
    wa
    #
    wa
    @14
    @13
    @4
    @15
    @16
    @16
    @7
    @4
    @15
    @7
    @6
    vk
    c0
    c1o
    cpr
    #
    wral
    @16
    @6
    vk
    c2o
    @17
    df2o3
    raleqi
    @6
    @10
    @12
    vk
    c0
    c1o
    0ex
    c1o
    con0
    1on
    elexi
    @1
    @5
    @9
    @2
    cA
    @0
    c0
    cG
    fveq2
    @1
    cA
    cB
    iftrue
    eleq12d
    @0
    c1o
    wceq
    #
    @5
    @11
    @2
    cB
    @0
    c1o
    cG
    fveq2
    @18
    @0
    c0
    wne
    #
    @2
    cB
    wceq
    @18
    @19
    c1o
    c0
    wne
    1n0
    @0
    c1o
    c0
    neeq1
    mpbiri
    @0
    c0
    cA
    cB
    ifnefalse
    syl
    eleq12d
    ralpr
    bitri
    @4
    @3
    @7
    @4
    cG
    cfn
    wcel
    #
    @3
    @4
    c2o
    cfn
    wcel
    #
    @20
    c2o
    com
    wcel
    @21
    2onn
    c2o
    nnfi
    ax-mp
    c2o
    cG
    fnfi
    mpan2
    cG
    cfn
    elex
    syl
    biantrurd
    syl5rbbr
    pm5.32i
    @4
    @3
    @7
    3anass
    @4
    @10
    @12
    3anass
    3bitr4i
    bitri
    bitri
end
