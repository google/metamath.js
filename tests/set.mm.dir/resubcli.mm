include "cneg.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "cr.mm"
include "cc.mm"
include "wcel.mm"
include "wceq.mm"
include "recni.mm"
include "negsub.mm"
include "mp2an.mm"
include "renegcli.mm"
include "readdcli.mm"
include "eqeltrri.mm"

theorem resubcli
  let cA: class A
  let cB: class B
  let vx: setvar x
  assume renegcl.1: |- A e. RR
  assume resubcl.2: |- B e. RR


  assert |- ( A - B ) e. RR

  proof
    cA
    cB
    cneg
    #
    caddc
    co
    #
    cA
    cB
    cmin
    co
    #
    cr
    cA
    cc
    wcel
    cB
    cc
    wcel
    @1
    @2
    wceq
    cA
    renegcl.1
    recni
    cB
    resubcl.2
    recni
    cA
    cB
    negsub
    mp2an
    cA
    @0
    renegcl.1
    cB
    resubcl.2
    renegcli
    readdcli
    eqeltrri
end
