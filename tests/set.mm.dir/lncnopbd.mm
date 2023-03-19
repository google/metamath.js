include "clo.mm"
include "ccop.mm"
include "cin.mm"
include "wcel.mm"
include "wa.mm"
include "cbo.mm"
include "elin.mm"
include "lnopcnbd.mm"
include "biimpa.mm"
include "bdopln.mm"
include "biimparc.mm"
include "mpdan.mm"
include "jca.mm"
include "impbii.mm"
include "bitri.mm"

theorem lncnopbd
  let cT: class T


  assert |- ( T e. ( LinOp i^i ContOp ) <-> T e. BndLinOp )

  proof
    cT
    clo
    ccop
    cin
    wcel
    cT
    clo
    wcel
    #
    cT
    ccop
    wcel
    #
    wa
    #
    cT
    cbo
    wcel
    #
    cT
    clo
    ccop
    elin
    @2
    @3
    @0
    @1
    @3
    cT
    lnopcnbd
    #
    biimpa
    @3
    @0
    @1
    cT
    bdopln
    #
    @3
    @0
    @1
    @5
    @0
    @1
    @3
    @4
    biimparc
    mpdan
    jca
    impbii
    bitri
end
