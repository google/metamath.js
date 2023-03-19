include "cn.mm"
include "csquarenn.mm"
include "cdif.mm"
include "wcel.mm"
include "cpell14qr.mm"
include "cfv.mm"
include "cpell1234qr.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "pell14qrss1234.mm"
include "sselda.mm"
include "pell14qrgt0.mm"
include "jca.mm"
include "cneg.mm"
include "wn.mm"
include "wo.mm"
include "cr.mm"
include "wi.mm"
include "0re.mm"
include "pell1234qrre.mm"
include "ltnsym.mm"
include "sylancr.mm"
include "impr.mm"
include "adantrr.mm"
include "lt0neg1d.mm"
include "mtbid.mm"
include "ex.mm"
include "adantr.mm"
include "mtod.mm"
include "pell1234qrdich.mm"
include "orel2.mm"
include "sylc.mm"
include "impbida.mm"

theorem elpell14qr2
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


  assert |- ( D e. ( NN \ []NN ) -> ( A e. ( Pell14QR ` D ) <-> ( A e. ( Pell1234QR ` D ) /\ 0 < A ) ) )

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
    pell14qrss1234
    sselda
    cA
    cD
    pell14qrgt0
    jca
    @0
    @6
    wa
    #
    cA
    cneg
    #
    @1
    wcel
    #
    wn
    @2
    @9
    wo
    #
    @2
    @7
    @9
    cc0
    @8
    clt
    wbr
    #
    @7
    cA
    cc0
    clt
    wbr
    #
    @11
    @0
    @4
    @5
    @12
    wn
    #
    @0
    @4
    wa
    cc0
    cr
    wcel
    cA
    cr
    wcel
    #
    @5
    @13
    wi
    0re
    cA
    cD
    pell1234qrre
    #
    cc0
    cA
    ltnsym
    sylancr
    impr
    @7
    cA
    @0
    @4
    @14
    @5
    @15
    adantrr
    lt0neg1d
    mtbid
    @0
    @9
    @11
    wi
    @6
    @0
    @9
    @11
    @8
    cD
    pell14qrgt0
    ex
    adantr
    mtod
    @0
    @4
    @10
    @5
    cA
    cD
    pell1234qrdich
    adantrr
    @9
    @2
    orel2
    sylc
    impbida
end
