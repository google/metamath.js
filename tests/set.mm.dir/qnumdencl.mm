include "cq.mm"
include "wcel.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cgcd.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "cdiv.mm"
include "wa.mm"
include "cz.mm"
include "cn.mm"
include "cxp.mm"
include "crio.mm"
include "cnumer.mm"
include "cdenom.mm"
include "wreu.mm"
include "qredeu.mm"
include "riotacl.mm"
include "syl.mm"
include "cop.mm"
include "elxp6.mm"
include "qnumval.mm"
include "eleq1d.mm"
include "qdenval.mm"
include "anbi12d.mm"
include "biimprd.mm"
include "adantld.mm"
include "syl5bi.mm"
include "mpd.mm"

theorem qnumdencl
  let cA: class A
  let va: setvar a
  let vb: setvar b
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( A e. QQ -> ( ( numer ` A ) e. ZZ /\ ( denom ` A ) e. NN ) )

  proof
    cA
    cq
    wcel
    #
    va
    cv
    #
    c1st
    cfv
    #
    @1
    c2nd
    cfv
    #
    cgcd
    co
    c1
    wceq
    cA
    @2
    @3
    cdiv
    co
    wceq
    wa
    #
    va
    cz
    cn
    cxp
    #
    crio
    #
    @5
    wcel
    #
    cA
    cnumer
    cfv
    #
    cz
    wcel
    #
    cA
    cdenom
    cfv
    #
    cn
    wcel
    #
    wa
    #
    @0
    @4
    va
    @5
    wreu
    @7
    va
    cA
    qredeu
    @4
    va
    @5
    riotacl
    syl
    @7
    @6
    @6
    c1st
    cfv
    #
    @6
    c2nd
    cfv
    #
    cop
    wceq
    #
    @13
    cz
    wcel
    #
    @14
    cn
    wcel
    #
    wa
    #
    wa
    @0
    @12
    @6
    cz
    cn
    elxp6
    @0
    @18
    @12
    @15
    @0
    @12
    @18
    @0
    @9
    @16
    @11
    @17
    @0
    @8
    @13
    cz
    va
    cA
    qnumval
    eleq1d
    @0
    @10
    @14
    cn
    va
    cA
    qdenval
    eleq1d
    anbi12d
    biimprd
    adantld
    syl5bi
    mpd
end
