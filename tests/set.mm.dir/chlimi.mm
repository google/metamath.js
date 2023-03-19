include "cch.mm"
include "wcel.mm"
include "cn.mm"
include "wf.mm"
include "chli.mm"
include "wbr.mm"
include "cv.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "csh.mm"
include "isch2.mm"
include "simprbi.mm"
include "cvv.mm"
include "nnex.mm"
include "fex.mm"
include "mpan2.mm"
include "adantr.mm"
include "wceq.mm"
include "feq1.mm"
include "breq1.mm"
include "anbi12d.mm"
include "imbi1d.mm"
include "albidv.mm"
include "spcgv.mm"
include "breq2.mm"
include "anbi2d.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "spcv.mm"
include "syl6.mm"
include "syl.mm"
include "pm2.43b.mm"
include "3impib.mm"

theorem chlimi
  let cA: class A
  let cF: class F
  let cH: class H
  let vf: setvar f
  let vx: setvar x
  assume chlim.1: |- A e. _V


  assert |- ( ( H e. CH /\ F : NN --> H /\ F ~~>v A ) -> A e. H )

  proof
    cH
    cch
    wcel
    #
    cn
    cH
    cF
    wf
    #
    cF
    cA
    chli
    wbr
    #
    cA
    cH
    wcel
    #
    @0
    cn
    cH
    vf
    cv
    #
    wf
    #
    @4
    vx
    cv
    #
    chli
    wbr
    #
    wa
    #
    @6
    cH
    wcel
    #
    wi
    #
    vx
    wal
    #
    vf
    wal
    #
    @1
    @2
    wa
    #
    @3
    wi
    #
    @0
    cH
    csh
    wcel
    @12
    vx
    vf
    cH
    isch2
    simprbi
    @12
    @13
    @3
    @13
    cF
    cvv
    wcel
    #
    @12
    @14
    wi
    @1
    @15
    @2
    @1
    cn
    cvv
    wcel
    @15
    nnex
    cn
    cH
    cvv
    cF
    fex
    mpan2
    adantr
    @15
    @12
    @1
    cF
    @6
    chli
    wbr
    #
    wa
    #
    @9
    wi
    #
    vx
    wal
    #
    @14
    @11
    @19
    vf
    cF
    cvv
    @4
    cF
    wceq
    #
    @10
    @18
    vx
    @20
    @8
    @17
    @9
    @20
    @5
    @1
    @7
    @16
    cn
    cH
    @4
    cF
    feq1
    @4
    cF
    @6
    chli
    breq1
    anbi12d
    imbi1d
    albidv
    spcgv
    @18
    @14
    vx
    cA
    chlim.1
    @6
    cA
    wceq
    #
    @17
    @13
    @9
    @3
    @21
    @16
    @2
    @1
    @6
    cA
    cF
    chli
    breq2
    anbi2d
    @6
    cA
    cH
    eleq1
    imbi12d
    spcv
    syl6
    syl
    pm2.43b
    syl
    3impib
end
