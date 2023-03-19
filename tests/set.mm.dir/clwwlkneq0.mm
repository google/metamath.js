include "cvv.mm"
include "wnel.mm"
include "cn.mm"
include "wo.mm"
include "wcel.mm"
include "wn.mm"
include "cn0.mm"
include "cc0.mm"
include "wne.mm"
include "cclwwlkn.mm"
include "co.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "df-nel.mm"
include "ianor.mm"
include "orbi12i.mm"
include "elnnne0.mm"
include "xchbinx.mm"
include "orbi2i.mm"
include "orass.mm"
include "3bitr4i.mm"
include "orcom.mm"
include "bitri.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "cclwwlk.mm"
include "crab.mm"
include "df-clwwlkn.mm"
include "mpt2ndm0.mm"
include "sylbir.mm"
include "nne.mm"
include "oveq1.mm"
include "clwwlkn0.mm"
include "syl6eq.mm"
include "sylbi.mm"
include "jaoi.mm"

theorem clwwlkneq0
  let cG: class G
  let cN: class N
  let vg: setvar g
  let vn: setvar n
  let vw: setvar w


  assert |- ( ( G e/ _V \/ N e/ NN ) -> ( N ClWWalksN G ) = (/) )

  proof
    cG
    cvv
    wnel
    #
    cN
    cn
    wnel
    #
    wo
    #
    cG
    cvv
    wcel
    #
    wn
    #
    cN
    cn0
    wcel
    #
    wn
    #
    wo
    #
    cN
    cc0
    wne
    #
    wn
    #
    wo
    #
    cN
    cG
    cclwwlkn
    co
    #
    c0
    wceq
    #
    @0
    @5
    @8
    wa
    #
    wn
    #
    wo
    @4
    @6
    @9
    wo
    #
    wo
    @2
    @10
    @0
    @4
    @14
    @15
    cG
    cvv
    df-nel
    @5
    @8
    ianor
    orbi12i
    @1
    @14
    @0
    @1
    cN
    cn
    wcel
    @13
    cN
    cn
    df-nel
    cN
    elnnne0
    xchbinx
    orbi2i
    @4
    @6
    @9
    orass
    3bitr4i
    @7
    @12
    @9
    @7
    @5
    @3
    wa
    wn
    #
    @12
    @16
    @6
    @4
    wo
    @7
    @5
    @3
    ianor
    @6
    @4
    orcom
    bitri
    vn
    vg
    vw
    cv
    chash
    cfv
    vn
    cv
    wceq
    vw
    vg
    cv
    cclwwlk
    cfv
    crab
    cclwwlkn
    cN
    cG
    cn0
    cvv
    vw
    vg
    vn
    df-clwwlkn
    mpt2ndm0
    sylbir
    @9
    cN
    cc0
    wceq
    #
    @12
    cN
    cc0
    nne
    @17
    @11
    cc0
    cG
    cclwwlkn
    co
    c0
    cN
    cc0
    cG
    cclwwlkn
    oveq1
    cG
    clwwlkn0
    syl6eq
    sylbi
    jaoi
    sylbi
end
