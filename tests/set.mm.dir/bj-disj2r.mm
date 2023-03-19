include "cin.mm"
include "cdif.mm"
include "wss.mm"
include "wceq.mm"
include "c0.mm"
include "df-ss.mm"
include "indif2.mm"
include "inss1.mm"
include "ssid.mm"
include "inss2.mm"
include "ssini.mm"
include "eqssi.mm"
include "difeq1i.mm"
include "eqtri.mm"
include "eqeq1i.mm"
include "eqcom.mm"
include "3bitri.mm"
include "disj3.mm"
include "in32.mm"
include "3bitr2i.mm"

theorem bj-disj2r
  let cA: class A
  let cB: class B
  let cV: class V


  assert |- ( ( A i^i V ) C_ ( V \ B ) <-> ( ( A i^i B ) i^i V ) = (/) )

  proof
    cA
    cV
    cin
    #
    cV
    cB
    cdif
    #
    wss
    #
    @0
    @0
    cB
    cdif
    #
    wceq
    #
    @0
    cB
    cin
    #
    c0
    wceq
    cA
    cB
    cin
    cV
    cin
    #
    c0
    wceq
    @2
    @0
    @1
    cin
    #
    @0
    wceq
    @3
    @0
    wceq
    @4
    @0
    @1
    df-ss
    @7
    @3
    @0
    @7
    @0
    cV
    cin
    #
    cB
    cdif
    @3
    @0
    cV
    cB
    indif2
    @8
    @0
    cB
    @8
    @0
    @0
    cV
    inss1
    @0
    @0
    cV
    @0
    ssid
    cA
    cV
    inss2
    ssini
    eqssi
    difeq1i
    eqtri
    eqeq1i
    @3
    @0
    eqcom
    3bitri
    @0
    cB
    disj3
    @5
    @6
    c0
    cA
    cV
    cB
    in32
    eqeq1i
    3bitr2i
end
