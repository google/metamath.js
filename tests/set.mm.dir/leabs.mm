include "cr.mm"
include "wcel.mm"
include "cabs.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cc0.mm"
include "0red.mm"
include "id.mm"
include "wceq.mm"
include "absid.mm"
include "eqcom.mm"
include "eqle.mm"
include "sylan2b.mm"
include "syldan.mm"
include "cc.mm"
include "recn.mm"
include "absge0.mm"
include "syl.mm"
include "wa.mm"
include "wi.mm"
include "abscl.mm"
include "0re.mm"
include "letr.mm"
include "mp3an2.mm"
include "mpdan.mm"
include "mpan2d.mm"
include "imp.mm"
include "lecasei.mm"

theorem leabs
  let cA: class A


  assert |- ( A e. RR -> A <_ ( abs ` A ) )

  proof
    cA
    cr
    wcel
    #
    cA
    cA
    cabs
    cfv
    #
    cle
    wbr
    #
    cc0
    cA
    @0
    0red
    @0
    id
    @0
    cc0
    cA
    cle
    wbr
    @1
    cA
    wceq
    #
    @2
    cA
    absid
    @3
    @0
    cA
    @1
    wceq
    @2
    @1
    cA
    eqcom
    cA
    @1
    eqle
    sylan2b
    syldan
    @0
    cA
    cc0
    cle
    wbr
    #
    @2
    @0
    @4
    cc0
    @1
    cle
    wbr
    #
    @2
    @0
    cA
    cc
    wcel
    #
    @5
    cA
    recn
    #
    cA
    absge0
    syl
    @0
    @1
    cr
    wcel
    #
    @4
    @5
    wa
    @2
    wi
    #
    @0
    @6
    @8
    @7
    cA
    abscl
    syl
    @0
    cc0
    cr
    wcel
    @8
    @9
    0re
    cA
    cc0
    @1
    letr
    mp3an2
    mpdan
    mpan2d
    imp
    lecasei
end
