include "cfz.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "csn.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wcel.mm"
include "wn.mm"
include "cle.mm"
include "wbr.mm"
include "elfzle2.mm"
include "cr.mm"
include "elfzel2.mm"
include "zred.mm"
include "clt.mm"
include "ltp1.mm"
include "wb.mm"
include "peano2re.mm"
include "ltnle.mm"
include "mpdan.mm"
include "mpbid.mm"
include "syl.mm"
include "pm2.65i.mm"
include "disjsn.mm"
include "mpbir.mm"

theorem fzp1disj
  let cM: class M
  let cN: class N


  assert |- ( ( M ... N ) i^i { ( N + 1 ) } ) = (/)

  proof
    cM
    cN
    cfz
    co
    #
    cN
    c1
    caddc
    co
    #
    csn
    cin
    c0
    wceq
    @1
    @0
    wcel
    #
    wn
    @2
    @1
    cN
    cle
    wbr
    #
    @1
    cM
    cN
    elfzle2
    @2
    cN
    cr
    wcel
    #
    @3
    wn
    #
    @2
    cN
    @1
    cM
    cN
    elfzel2
    zred
    @4
    cN
    @1
    clt
    wbr
    #
    @5
    cN
    ltp1
    @4
    @1
    cr
    wcel
    @6
    @5
    wb
    cN
    peano2re
    cN
    @1
    ltnle
    mpdan
    mpbid
    syl
    pm2.65i
    @0
    @1
    disjsn
    mpbir
end
