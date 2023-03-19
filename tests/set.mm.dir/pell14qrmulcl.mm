include "cn.mm"
include "csquarenn.mm"
include "cdif.mm"
include "wcel.mm"
include "cpell14qr.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "cpell1234qr.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "simpl.mm"
include "simprll.mm"
include "simprrl.mm"
include "pell1234qrmulcl.mm"
include "syl3anc.mm"
include "cr.mm"
include "pell1234qrre.mm"
include "syldan.mm"
include "simprlr.mm"
include "simprrr.mm"
include "mulgt0d.mm"
include "jca.mm"
include "ex.mm"
include "elpell14qr2.mm"
include "anbi12d.mm"
include "3imtr4d.mm"
include "3impib.mm"

theorem pell14qrmulcl
  let cA: class A
  let cB: class B
  let cD: class D
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell14QR ` D ) /\ B e. ( Pell14QR ` D ) ) -> ( A x. B ) e. ( Pell14QR ` D ) )

  proof
    cD
    cn
    csquarenn
    cdif
    wcel
    #
    cA
    cD
    cpell14qr
    cfv
    #
    wcel
    #
    cB
    @1
    wcel
    #
    cA
    cB
    cmul
    co
    #
    @1
    wcel
    #
    @0
    cA
    cD
    cpell1234qr
    cfv
    #
    wcel
    #
    cc0
    cA
    clt
    wbr
    #
    wa
    #
    cB
    @6
    wcel
    #
    cc0
    cB
    clt
    wbr
    #
    wa
    #
    wa
    #
    @4
    @6
    wcel
    #
    cc0
    @4
    clt
    wbr
    #
    wa
    #
    @2
    @3
    wa
    @5
    @0
    @13
    @16
    @0
    @13
    wa
    #
    @14
    @15
    @17
    @0
    @7
    @10
    @14
    @0
    @13
    simpl
    @0
    @7
    @8
    @12
    simprll
    #
    @0
    @9
    @10
    @11
    simprrl
    #
    cA
    cB
    cD
    pell1234qrmulcl
    syl3anc
    @17
    cA
    cB
    @0
    @13
    @7
    cA
    cr
    wcel
    @18
    cA
    cD
    pell1234qrre
    syldan
    @0
    @13
    @10
    cB
    cr
    wcel
    @19
    cB
    cD
    pell1234qrre
    syldan
    @0
    @7
    @8
    @12
    simprlr
    @0
    @9
    @10
    @11
    simprrr
    mulgt0d
    jca
    ex
    @0
    @2
    @9
    @3
    @12
    cA
    cD
    elpell14qr2
    cB
    cD
    elpell14qr2
    anbi12d
    @4
    cD
    elpell14qr2
    3imtr4d
    3impib
end
