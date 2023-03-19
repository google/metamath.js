include "cn0.mm"
include "wcel.mm"
include "cvv.mm"
include "wa.mm"
include "cclwwlkn.mm"
include "co.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "cclwwlk.mm"
include "crab.mm"
include "fveq2.mm"
include "adantl.mm"
include "wb.mm"
include "eqeq2.mm"
include "adantr.mm"
include "rabeqbidv.mm"
include "df-clwwlkn.mm"
include "fvex.mm"
include "rabex.mm"
include "ovmpt2a.mm"
include "wn.mm"
include "c0.mm"
include "mpt2ndm0.mm"
include "wo.mm"
include "wral.mm"
include "cvtx.mm"
include "cword.mm"
include "wne.mm"
include "eqid.mm"
include "clwwlkbp.mm"
include "simp2d.mm"
include "lencl.mm"
include "syl.mm"
include "eleq1.mm"
include "syl5ibcom.mm"
include "con3rr3.mm"
include "ralrimiv.mm"
include "ral0.mm"
include "fvprc.mm"
include "raleqdv.mm"
include "mpbiri.mm"
include "jaoi.mm"
include "ianor.mm"
include "rabeq0.mm"
include "3imtr4i.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"

theorem clwwlkn
  let vw: setvar w
  let cG: class G
  let cN: class N
  let vg: setvar g
  let vn: setvar n

  disjoint G w
  disjoint N w
  disjoint G g
  disjoint G n
  disjoint g n
  disjoint g w
  disjoint n w
  disjoint N g
  disjoint N n
  assert |- ( N ClWWalksN G ) = { w e. ( ClWWalks ` G ) | ( # ` w ) = N }

  proof
    cN
    cn0
    wcel
    #
    cG
    cvv
    wcel
    #
    wa
    #
    cN
    cG
    cclwwlkn
    co
    #
    vw
    cv
    #
    chash
    cfv
    #
    cN
    wceq
    #
    vw
    cG
    cclwwlk
    cfv
    #
    crab
    #
    wceq
    vn
    vg
    cN
    cG
    cn0
    cvv
    @5
    vn
    cv
    #
    wceq
    #
    vw
    vg
    cv
    #
    cclwwlk
    cfv
    #
    crab
    #
    @8
    cclwwlkn
    @9
    cN
    wceq
    #
    @11
    cG
    wceq
    #
    wa
    @10
    @6
    vw
    @12
    @7
    @15
    @12
    @7
    wceq
    @14
    @11
    cG
    cclwwlk
    fveq2
    adantl
    @14
    @10
    @6
    wb
    @15
    @9
    cN
    @5
    eqeq2
    adantr
    rabeqbidv
    vw
    vg
    vn
    df-clwwlkn
    #
    @6
    vw
    @7
    cG
    cclwwlk
    fvex
    rabex
    ovmpt2a
    @2
    wn
    #
    @3
    c0
    @8
    vn
    vg
    @13
    cclwwlkn
    cN
    cG
    cn0
    cvv
    @16
    mpt2ndm0
    @0
    wn
    #
    @1
    wn
    #
    wo
    @6
    wn
    #
    vw
    @7
    wral
    #
    @17
    @8
    c0
    wceq
    @18
    @21
    @19
    @18
    @20
    vw
    @7
    @4
    @7
    wcel
    #
    @6
    @0
    @22
    @5
    cn0
    wcel
    #
    @6
    @0
    @22
    @4
    cG
    cvtx
    cfv
    #
    cword
    wcel
    #
    @23
    @22
    @1
    @25
    @4
    c0
    wne
    cG
    @24
    @4
    @24
    eqid
    clwwlkbp
    simp2d
    @24
    @4
    lencl
    syl
    @5
    cN
    cn0
    eleq1
    syl5ibcom
    con3rr3
    ralrimiv
    @19
    @21
    @20
    vw
    c0
    wral
    @20
    vw
    ral0
    @19
    @20
    vw
    @7
    c0
    cG
    cclwwlk
    fvprc
    raleqdv
    mpbiri
    jaoi
    @0
    @1
    ianor
    @6
    vw
    @7
    rabeq0
    3imtr4i
    eqtr4d
    pm2.61i
end
