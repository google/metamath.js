include "cz.mm"
include "wcel.mm"
include "cfz.mm"
include "co.mm"
include "caddc.mm"
include "cmin.mm"
include "w3a.mm"
include "wa.mm"
include "simpl.mm"
include "elfzel1.mm"
include "adantl.mm"
include "elfzel2.mm"
include "3jca.mm"
include "wb.mm"
include "cc.mm"
include "wceq.mm"
include "zcn.mm"
include "pncan.mm"
include "pncan2.mm"
include "oveq12d.mm"
include "syl2an.mm"
include "eleq2d.mm"
include "3adant1.mm"
include "3simpc.mm"
include "zaddcl.mm"
include "simp1.mm"
include "fzrev.mm"
include "syl12anc.mm"
include "bitr3d.mm"
include "pm5.21nd.mm"

theorem fzrev3
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( K e. ZZ -> ( K e. ( M ... N ) <-> ( ( M + N ) - K ) e. ( M ... N ) ) )

  proof
    cK
    cz
    wcel
    #
    cK
    cM
    cN
    cfz
    co
    #
    wcel
    #
    cM
    cN
    caddc
    co
    #
    cK
    cmin
    co
    #
    @1
    wcel
    #
    @0
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    w3a
    #
    @0
    @2
    wa
    @0
    @6
    @7
    @0
    @2
    simpl
    @2
    @6
    @0
    cK
    cM
    cN
    elfzel1
    adantl
    @2
    @7
    @0
    cK
    cM
    cN
    elfzel2
    adantl
    3jca
    @0
    @5
    wa
    @0
    @6
    @7
    @0
    @5
    simpl
    @5
    @6
    @0
    @4
    cM
    cN
    elfzel1
    adantl
    @5
    @7
    @0
    @4
    cM
    cN
    elfzel2
    adantl
    3jca
    @8
    cK
    @3
    cN
    cmin
    co
    #
    @3
    cM
    cmin
    co
    #
    cfz
    co
    #
    wcel
    #
    @2
    @5
    @6
    @7
    @12
    @2
    wb
    @0
    @6
    @7
    wa
    #
    @11
    @1
    cK
    @6
    cM
    cc
    wcel
    #
    cN
    cc
    wcel
    #
    @11
    @1
    wceq
    @7
    cM
    zcn
    cN
    zcn
    @14
    @15
    wa
    @9
    cM
    @10
    cN
    cfz
    cM
    cN
    pncan
    cM
    cN
    pncan2
    oveq12d
    syl2an
    eleq2d
    3adant1
    @8
    @13
    @3
    cz
    wcel
    #
    @0
    @12
    @5
    wb
    @0
    @6
    @7
    3simpc
    @6
    @7
    @16
    @0
    cM
    cN
    zaddcl
    3adant1
    @0
    @6
    @7
    simp1
    @3
    cK
    cM
    cN
    fzrev
    syl12anc
    bitr3d
    pm5.21nd
end
