include "cn.mm"
include "csquarenn.mm"
include "cdif.mm"
include "wcel.mm"
include "cpell1qr.mm"
include "cfv.mm"
include "cpell14qr.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "pell1qrss14.mm"
include "sselda.mm"
include "pell1qrge1.mm"
include "jca.mm"
include "clt.mm"
include "wceq.mm"
include "wo.mm"
include "1red.mm"
include "pell14qrre.mm"
include "leloed.mm"
include "cdiv.mm"
include "co.mm"
include "wn.mm"
include "ltnled.mm"
include "biimpa.mm"
include "1div1e1.mm"
include "eqcomi.mm"
include "a1i.mm"
include "breq2d.mm"
include "cr.mm"
include "cc0.mm"
include "wb.mm"
include "adantr.mm"
include "pell14qrgt0.mm"
include "0lt1.mm"
include "lerec2.mm"
include "syl22anc.mm"
include "bitrd.mm"
include "mtbid.mm"
include "simplll.mm"
include "sylancom.mm"
include "mtand.mm"
include "pell14qrdich.mm"
include "orel2.mm"
include "sylc.mm"
include "simpr.mm"
include "pell1qr1.mm"
include "ad2antrr.mm"
include "eqeltrrd.mm"
include "jaodan.mm"
include "ex.mm"
include "sylbid.mm"
include "impr.mm"
include "impbida.mm"

theorem elpell1qr2
  let cA: class A
  let cD: class D
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let cB: class B
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( D e. ( NN \ []NN ) -> ( A e. ( Pell1QR ` D ) <-> ( A e. ( Pell14QR ` D ) /\ 1 <_ A ) ) )

  proof
    cD
    cn
    csquarenn
    cdif
    wcel
    #
    cA
    cD
    cpell1qr
    cfv
    #
    wcel
    #
    cA
    cD
    cpell14qr
    cfv
    #
    wcel
    #
    c1
    cA
    cle
    wbr
    #
    wa
    @0
    @2
    wa
    @4
    @5
    @0
    @1
    @3
    cA
    cD
    pell1qrss14
    sselda
    cA
    cD
    pell1qrge1
    jca
    @0
    @4
    @5
    @2
    @0
    @4
    wa
    #
    @5
    c1
    cA
    clt
    wbr
    #
    c1
    cA
    wceq
    #
    wo
    #
    @2
    @6
    c1
    cA
    @6
    1red
    #
    cA
    cD
    pell14qrre
    #
    leloed
    @6
    @9
    @2
    @6
    @7
    @2
    @8
    @6
    @7
    wa
    #
    c1
    cA
    cdiv
    co
    #
    @1
    wcel
    #
    wn
    @2
    @14
    wo
    #
    @2
    @12
    @14
    c1
    @13
    cle
    wbr
    #
    @12
    cA
    c1
    cle
    wbr
    #
    @16
    @6
    @7
    @17
    wn
    @6
    c1
    cA
    @10
    @11
    ltnled
    biimpa
    @12
    @17
    cA
    c1
    c1
    cdiv
    co
    #
    cle
    wbr
    #
    @16
    @12
    c1
    @18
    cA
    cle
    c1
    @18
    wceq
    @12
    @18
    c1
    1div1e1
    eqcomi
    a1i
    breq2d
    @12
    cA
    cr
    wcel
    #
    cc0
    cA
    clt
    wbr
    #
    c1
    cr
    wcel
    cc0
    c1
    clt
    wbr
    #
    @19
    @16
    wb
    @6
    @20
    @7
    @11
    adantr
    @6
    @21
    @7
    cA
    cD
    pell14qrgt0
    adantr
    @12
    1red
    @22
    @12
    0lt1
    a1i
    cA
    c1
    lerec2
    syl22anc
    bitrd
    mtbid
    @12
    @14
    @0
    @16
    @0
    @4
    @7
    @14
    simplll
    @13
    cD
    pell1qrge1
    sylancom
    mtand
    @6
    @15
    @7
    cA
    cD
    pell14qrdich
    adantr
    @14
    @2
    orel2
    sylc
    @6
    @8
    wa
    c1
    cA
    @1
    @6
    @8
    simpr
    @0
    c1
    @1
    wcel
    @4
    @8
    cD
    pell1qr1
    ad2antrr
    eqeltrrd
    jaodan
    ex
    sylbid
    impr
    impbida
end
