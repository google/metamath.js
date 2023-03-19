include "cin.mm"
include "cort.mm"
include "cfv.mm"
include "cmd.mm"
include "wbr.mm"
include "cdmd.mm"
include "wss.mm"
include "chj.mm"
include "co.mm"
include "wb.mm"
include "chincli.mm"
include "mdoc1i.mm"
include "dmdoc2i.mm"
include "ssid.mm"
include "chil.mm"
include "chjcli.mm"
include "chssii.mm"
include "chjoi.mm"
include "sseqtr4i.mm"
include "choccli.mm"
include "mdsldmd1i.mm"
include "mp4an.mm"

theorem dmdcompli
  let cA: class A
  let cB: class B
  assume mdcompl.1: |- A e. CH
  assume mdcompl.2: |- B e. CH


  assert |- ( A MH* B <-> ( A i^i ( _|_ ` ( A i^i B ) ) ) MH* ( B i^i ( _|_ ` ( A i^i B ) ) ) )

  proof
    cA
    cB
    cin
    #
    @0
    cort
    cfv
    #
    cmd
    wbr
    @1
    @0
    cdmd
    wbr
    @0
    @0
    wss
    cA
    cB
    chj
    co
    #
    @0
    @1
    chj
    co
    #
    wss
    cA
    cB
    cdmd
    wbr
    cA
    @1
    cin
    cB
    @1
    cin
    cdmd
    wbr
    wb
    @0
    cA
    cB
    mdcompl.1
    mdcompl.2
    chincli
    #
    mdoc1i
    @0
    @4
    dmdoc2i
    @0
    ssid
    @2
    chil
    @3
    @2
    cA
    cB
    mdcompl.1
    mdcompl.2
    chjcli
    chssii
    @0
    @4
    chjoi
    sseqtr4i
    @0
    @1
    cA
    cB
    @4
    @0
    @4
    choccli
    mdcompl.1
    mdcompl.2
    mdsldmd1i
    mp4an
end
