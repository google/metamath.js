include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "c1.mm"
include "cmin.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "wceq.mm"
include "csn.mm"
include "cun.mm"
include "wi.mm"
include "cz.mm"
include "caddc.mm"
include "cuz.mm"
include "cfv.mm"
include "0z.mm"
include "cn0.mm"
include "cn.mm"
include "w3a.mm"
include "elfzo0.mm"
include "elnnuz.mm"
include "biimpi.mm"
include "0p1e1.mm"
include "a1i.mm"
include "fveq2d.mm"
include "eleqtrrd.mm"
include "3ad2ant2.mm"
include "sylbi.mm"
include "fzosplitsnm1.mm"
include "sylancr.mm"
include "eleq2.mm"
include "wo.mm"
include "elun.mm"
include "pm2.24.mm"
include "3ad2ant3.mm"
include "elsni.mm"
include "a1d.mm"
include "jaoi.mm"
include "syl6bi.mm"
include "mpcom.mm"
include "imp.mm"

theorem elfzonlteqm1
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ( 0 ..^ B ) /\ -. A < ( B - 1 ) ) -> A = ( B - 1 ) )

  proof
    cA
    cc0
    cB
    cfzo
    co
    #
    wcel
    #
    cA
    cB
    c1
    cmin
    co
    #
    clt
    wbr
    #
    wn
    #
    cA
    @2
    wceq
    #
    @0
    cc0
    @2
    cfzo
    co
    #
    @2
    csn
    #
    cun
    #
    wceq
    #
    @1
    @4
    @5
    wi
    #
    @1
    cc0
    cz
    wcel
    cB
    cc0
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    wcel
    #
    @9
    0z
    @1
    cA
    cn0
    wcel
    #
    cB
    cn
    wcel
    #
    cA
    cB
    clt
    wbr
    #
    w3a
    @13
    cA
    cB
    elfzo0
    @15
    @14
    @13
    @16
    @15
    cB
    c1
    cuz
    cfv
    #
    @12
    @15
    cB
    @17
    wcel
    cB
    elnnuz
    biimpi
    @15
    @11
    c1
    cuz
    @11
    c1
    wceq
    @15
    0p1e1
    a1i
    fveq2d
    eleqtrrd
    3ad2ant2
    sylbi
    cc0
    cB
    fzosplitsnm1
    sylancr
    @9
    @1
    cA
    @8
    wcel
    #
    @10
    @0
    @8
    cA
    eleq2
    @18
    cA
    @6
    wcel
    #
    cA
    @7
    wcel
    #
    wo
    @10
    cA
    @6
    @7
    elun
    @19
    @10
    @20
    @19
    @14
    @2
    cn
    wcel
    #
    @3
    w3a
    @10
    cA
    @2
    elfzo0
    @3
    @14
    @10
    @21
    @3
    @5
    pm2.24
    3ad2ant3
    sylbi
    @20
    @5
    @4
    cA
    @2
    elsni
    a1d
    jaoi
    sylbi
    syl6bi
    mpcom
    imp
end
